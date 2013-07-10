{-# LANGUAGE ForeignFunctionInterface, EmptyDataDecls, MagicHash, OverloadedStrings, UnboxedTuples #-}

#define _GNU_SOURCE

#include "Rts.h"
#include <dlfcn.h>

import qualified Data.ByteString as BS
import Control.Concurrent
import Control.Exception
import Foreign.Storable
import Foreign.C
import Foreign.Ptr
import System.Mem
import Control.Monad
import Text.Printf
import Foreign.Marshal.Array
import GHC.Prim
import GHC.Ptr
import Unsafe.Coerce
import GHC.HeapView
import System.IO.Unsafe
import Foreign.Marshal.Alloc
import Data.Elf
import System.Environment.Executable
import Data.List
import qualified Data.IntMap as IntMap

data Bdescr
data Dl_info

bdescrStart, bdescrFree :: Ptr Bdescr -> IO (Ptr a)
bdescrStart = #{peek bdescr, start}
bdescrFree = #{peek bdescr, free}

bdescrLink :: Ptr Bdescr -> IO (Ptr Bdescr)
bdescrLink = #{peek bdescr, link}

-- r17s_info
{-# NOINLINE nerf #-}
nerf = unsafePerformIO (putStrLn "NERF should be above the line" >> return (2 :: Int))

-- same bittedness only please!
elf = IntMap.fromList . concatMap (\e ->
            case snd (steName e) of
                Nothing -> []
                Just v -> [(unsafeCoerce (steValue e) :: Int, v)])
            . concat . parseSymbolTables . parseElf $ unsafePerformIO (BS.readFile =<< getExecutablePath)

lookupElf x = IntMap.lookup (fromIntegral (ptrToIntPtr x)) elf


main = do
    poke record_static 1
    performGC
    sol <- peek recorded_static_object_list
    let go p = do
        start <- bdescrStart p
        free <-  bdescrFree p
        let length = minusPtr free start `div` sizeOf (undefined :: Ptr a)
        xs <- peekArray length start :: IO [Ptr (Ptr Any)]
        -- printf "bd = %s (start = %s, free = %s)\n" (show p) (show start) (show free)
        forM_ xs $ \(Ptr a) ->
            -- unsafeCoerce should become a no-op
            -- p <- peek x
            -- print (IntMap.lookup (fromIntegral (ptrToIntPtr x)) elf)
            {-
            let b = IntMap.lookup (fromIntegral (ptrToIntPtr x)) elf == Just "r17s_closure"
            when b $ do
                symlookup x
                putStrLn "Bang" >> print (unsafeCoerce x :: Int)
                -}
            -- print =<< symlookup p
            -- (ptr, _, _) <- getClosureRaw (unsafeCoerce x :: Any)
            case addrToAny## a of
                (## v ##) -> forkIO $ primDeepEvaluate (Box v) `catch` (\(SomeException _) -> return ())
        next <- bdescrLink p
        when (next /= nullPtr) (go next)
    go sol
    freeRecordedStaticObjectList
    putStrLn "------------------"
    print nerf

-- like evaluate . rnf, but requires no type class instance
primDeepEvaluate :: Box -> IO ()
primDeepEvaluate x = do
    let force = case x of Box a -> evaluate a >> primDeepEvaluate x
    closure <- getBoxedClosureData x
    -- putStrLn (takeWhile (/=' ') (show closure))
    case closure of
        ConsClosure {ptrArgs = ps} -> mapM_ primDeepEvaluate ps
        ThunkClosure {} -> force
        SelectorClosure {} -> force
        IndClosure {indirectee = p} -> primDeepEvaluate p
        -- this case is tricky!!!
        BlackholeClosure {} -> do
        {-
            (info, _, _) <- case x of Box a -> getClosureRaw a
            print x
            print =<< symlookup info
            -}
            force
        APClosure {fun = p, payload = ps} -> mapM_ primDeepEvaluate (p:ps)
        PAPClosure {fun = p, payload = ps} -> mapM_ primDeepEvaluate (p:ps)
        APStackClosure {fun = p, payload = ps} -> mapM_ primDeepEvaluate (p:ps)
        -- do not look into mutable variables
        ArrWordsClosure {} -> return ()
        MutArrClosure {mccPayload = ps} -> return ()
        MutVarClosure {var = p} -> return ()
        MVarClosure {value = p} -> return ()
        FunClosure {ptrArgs = ps} -> mapM_ primDeepEvaluate ps
        _ -> return ()

symlookup :: Ptr a -> IO (Maybe String)
symlookup p = do
    allocaBytes #{size Dl_info} $ \info -> do
        r <- dladdr p info
        if (r == 0)
            then return Nothing
            else do
                sname <- #{peek Dl_info, dli_sname} info
                if sname == nullPtr
                    then return Nothing
                    else do
                        name <- peekCString sname
                        return (Just name)

foreign import ccall "&record_static" record_static :: Ptr CInt
foreign import ccall "&recorded_static_object_list" recorded_static_object_list :: Ptr (Ptr Bdescr)
foreign import ccall "freeRecordedStaticObjectList" freeRecordedStaticObjectList :: IO ()

foreign import ccall "dladdr" dladdr :: Ptr a -> Ptr Dl_info -> IO CInt
{-
           typedef struct {
               const char *dli_fname;  /* Pathname of shared object that
                                          contains address */
               void       *dli_fbase;  /* Address at which shared object
                                          is loaded */
               const char *dli_sname;  /* Name of nearest symbol with address
                                          lower than addr */
               void       *dli_saddr;  /* Exact address of symbol named
                                          in dli_sname */
           } Dl_info;
           -}

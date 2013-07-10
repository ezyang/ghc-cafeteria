{-# LANGUAGE ForeignFunctionInterface, EmptyDataDecls, MagicHash, OverloadedStrings, UnboxedTuples #-}

#define _GNU_SOURCE

#include "Rts.h"

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Control.Concurrent
import Control.Exception
import Foreign.Storable
import Foreign.C
import Foreign.Ptr
import System.Mem
import Control.Monad
import Foreign.Marshal.Array
import GHC.Prim
import GHC.Ptr
import Unsafe.Coerce
import System.IO.Unsafe
import System.Environment.Executable
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)

import Data.Elf
import GHC.HeapView

data Bdescr

bdescrStart, bdescrFree :: Ptr Bdescr -> IO (Ptr a)
bdescrStart = #{peek bdescr, start}
bdescrFree = #{peek bdescr, free}
bdescrLink :: Ptr Bdescr -> IO (Ptr Bdescr)
bdescrLink = #{peek bdescr, link}

{-# NOINLINE exampleCAF #-}
exampleCAF :: Int
exampleCAF = unsafePerformIO $ do
    putStrLn "This CAF should be evaluated before we reach the end of the program"
    return 2

-- debugging assistance for finding out what the static thing is

-- same bittedness only please!
globalSymbolTable :: IntMap ByteString
globalSymbolTable
  = IntMap.fromList
  . concatMap (\e -> case snd (steName e) of
      Nothing -> []
      Just v -> [(unsafeCoerce (steValue e) :: Int, v)])
  . concat
  . parseSymbolTables
  . parseElf
  $ unsafePerformIO (BS.readFile =<< getExecutablePath)

lookupSymbol :: Ptr a -> Maybe ByteString
lookupSymbol x = IntMap.lookup (fromIntegral (ptrToIntPtr x)) globalSymbolTable

main :: IO ()
main = do
    sol <- recordStaticObjectList
    let go p = do
        start <- bdescrStart p
        pfree <-  bdescrFree p
        let len = minusPtr pfree start `div` sizeOf (undefined :: Ptr a)
        xs <- peekArray len start
        forM_ xs $ \x@(Ptr a) -> do
            print (lookupSymbol x)
            case addrToAny## a of
                -- seems to go faster when you use forkIO. Probably should
                -- synchronize though
                (## v ##) -> forkIO $ primDeepEvaluate (Box v)
                                        -- need to catch exceptions since a lot of
                                        -- CAFs are things like 'error "WHOOPS"'
                                        `catch` (\(SomeException _) -> return ())
        next <- bdescrLink p
        when (next /= nullPtr) $ go next
    go sol
    freeRecordedStaticObjectList
    putStrLn "------------------"
    print exampleCAF

-- like evaluate . rnf, but requires no type class instance
primDeepEvaluate :: Box -> IO ()
primDeepEvaluate x = do
    let force = case x of Box a -> evaluate a >> primDeepEvaluate x
        evalAll = mapM_ primDeepEvaluate
    closure <- getBoxedClosureData x
    case closure of
        ThunkClosure {} -> force
        SelectorClosure {} -> force
        -- forcing a blackhole causes us to WAIT for the true thread.
        -- This should essentially never happen because we're supposed to
        -- be evaluating CAFs first, but who knows!
        BlackholeClosure {} -> force
        IndClosure {indirectee = p} -> primDeepEvaluate p
        ConsClosure {ptrArgs = ps} -> evalAll ps
        FunClosure {ptrArgs = ps} -> evalAll ps
        -- gotta do these because some "mutable arrays" are actually
        -- frozen and thus immutable, and SafeHaskell may allow these
        -- I think ghc-heap-view is MISSING SOME
        MutArrClosure {mccPayload = ps} -> evalAll ps
        APClosure {fun = p, payload = ps} -> evalAll (p:ps)
        PAPClosure {fun = p, payload = ps} -> evalAll (p:ps)
        APStackClosure {fun = p, payload = ps} -> evalAll (p:ps)
        -- unenterable stuff and mutable stuff
        _ -> return ()

-- make sure you free!
recordStaticObjectList :: IO (Ptr Bdescr)
recordStaticObjectList = do
    poke record_static 1
    performGC
    peek recorded_static_object_list

foreign import ccall "&record_static" record_static :: Ptr CInt
foreign import ccall "&recorded_static_object_list" recorded_static_object_list :: Ptr (Ptr Bdescr)
foreign import ccall "freeRecordedStaticObjectList" freeRecordedStaticObjectList :: IO ()

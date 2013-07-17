{-# LANGUAGE ForeignFunctionInterface, EmptyDataDecls, MagicHash, OverloadedStrings, UnboxedTuples #-}

#define _GNU_SOURCE

#include "Rts.h"

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
import System.IO.Unsafe
import System.IO
import Data.Bits
import Data.Word
import Data.List
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8

import GHC.HeapView

import SymLookup

data Bdescr

bdescrStart, bdescrFree :: Ptr Bdescr -> IO (Ptr a)
bdescrStart = #{peek bdescr, start}
bdescrFree = #{peek bdescr, free}
bdescrLink :: Ptr Bdescr -> IO (Ptr Bdescr)
bdescrLink = #{peek bdescr, link}

-- Thread bombing the Haskell runtime ends up being a bad idea.
-- However, we want this to be greater than one so that infinite
-- loops don't halt processing.
number_of_workers = 6

{-# NOINLINE exampleCAF #-}
exampleCAF :: Int
exampleCAF = unsafePerformIO (putStrLn "XXX" >> return 2)

{-# NOINLINE out #-}
out = unsafePerformIO (newMVar ())
sync = withMVar out . const

main :: IO ()
main = do
    -- This is pretty important: when a CAF gets overwritten
    -- with a result (even an indirection), the SRT of the original
    -- info table dies.  However, these pointers could be resurrected
    -- by a makeNonUpdatable, in which case a GC may have collected
    -- some static object that we need now.  Once we can guarantee
    -- no pointers are going to be made non-updatable, we can turn
    -- this off (but we don't, at the moment).  Note that the
    -- static object list (which is currently scavenged by the GC)
    -- is not sufficient, unless we update it to scavenge SRTs.
    setKeepCAFs
    hSetBuffering stdout NoBuffering
    sol <- recordStaticObjectList
    let process x@(Ptr a) = do
        -- let cond = orig_sym == Just "rceE_closure"
        let cond = False
        case addrToAny## a of
          (## v ##) -> do
            wait <- newEmptyMVar
            t <- forkIO $ staticEvaluate cond x (Box v)
                        -- need to catch exceptions since a lot of
                        -- CAFs are things like 'error ...'
                        `catch` (\(SomeException _) -> return ())
                        `finally` putMVar wait ()
            _ <- forkIO $ do
                threadDelay (1000000 `div` 2) -- in seconds
                m <- tryTakeMVar wait
                when (m == Nothing) $ do
                killThread t -- wait is now filled (if it's not we'll deadlock)
                -- print some debugging information
                Just orig_sym <- lookupSymbol x
                Just new_sym <- lookupSymbol =<< #{peek StgIndStatic, noupd_info} x
                sync $ putStrLn ("\n" ++ B8.unpack orig_sym ++ " -> " ++ B8.unpack new_sym)
                -- make it non-updatable
                makeNonUpdatable x
            readMVar wait
            sync (putStr ".")
    chan <- newChan
    let worker = do
        r <- readChan chan
        case r of
            Nothing -> return ()
            Just x -> process x >> worker
    let go p = do
        start <- bdescrStart p
        pfree <- bdescrFree p
        let len = minusPtr pfree start `div` sizeOf (undefined :: Ptr a)
        sync $ putStrLn ("Adding " ++ show len ++ " static objects")
        mapM_ (writeChan chan . Just) =<< peekArray len start
        next <- bdescrLink p
        when (next /= nullPtr) (go next)
    waits <- replicateM number_of_workers $ do
        wait <- newEmptyMVar
        _ <- forkIO (worker >> putMVar wait ())
        return wait
    go sol
    -- we can free this list immediately because we're saving CAFs
    freeRecordedStaticObjectList
    replicateM_ number_of_workers (writeChan chan Nothing)
    mapM_ takeMVar waits
    putStrLn "\n------------------"
    print exampleCAF

makeNonUpdatable :: Ptr a -> IO ()
makeNonUpdatable x = do
    noupd_info <- #{peek StgIndStatic, noupd_info} x
    when (noupd_info /= nullPtr) $ poke (castPtr x) noupd_info

-- We have an object which is known to be a CAF (since it came off
-- the static objects list).  How much of it do we have to evaluate?
-- Here is an important observation: any pointers contained by a CAF
-- must also be CAFs, and thus show up on the static objects list.
-- Thus, we don't need to, say, follow constructors (and indeed, we MUST
-- NOT do so, because that will lead to exponential time forcing things.)
-- So the only orders of business are to force things that need forcing,
-- and follow things that will have dynamic destinations (in particular,
-- indirections.)
staticEvaluate :: Bool -> Ptr a -> Box -> IO ()
staticEvaluate cond p x = do
    let force = do
        x' <- case x of Box a -> evaluate a
        primDeepEvaluate cond (asBox x')
    closure <- getBoxedClosureData x
    case closure of
        ThunkClosure {} -> force
        BlackholeClosure {} -> force
        IndClosure {indirectee = p} -> primDeepEvaluate cond p
        _ -> error $ "staticEvaluate: strange closure type " ++ show closure

printClosure x = sync $ do
    (infotable, ws, _) <- case x of Box a -> getClosureRaw a
    Just info_name <- lookupSymbol (#{ptr StgInfoTable, code} infotable)
    putStr ("\n" ++ B8.unpack info_name ++ " " ++ intercalate " " (map (show . wordPtrToPtr . fromIntegral) (tail ws)))

-- Like evaluate . rnf, but it requires no type class instances.
primDeepEvaluate :: Bool -> Box -> IO ()
primDeepEvaluate cond x = do
    let force = primDeepEvaluate cond . asBox =<< case x of Box a -> evaluate a
        evalAll = mapM_ (primDeepEvaluate cond)
    closure <- getBoxedClosureData x
    when cond $ printClosure x
    case tipe (info closure) of
        -- skip static data, we trust in staticEvaluate to handle these
        CONSTR_STATIC -> return ()
        CONSTR_NOCAF_STATIC -> return ()
        FUN_STATIC -> return ()
        THUNK_STATIC -> return ()
        IND_STATIC -> return ()
        _ -> case closure of
                ThunkClosure     {} -> force
                SelectorClosure  {} -> force
                BlackholeClosure {indirectee = p}  -> force
                IndClosure       {indirectee = p}  -> primDeepEvaluate cond p
                ConsClosure      {ptrArgs = ps}    -> evalAll ps
                FunClosure       {ptrArgs = ps}    -> evalAll ps
                -- We try not to do mutable things, but frozen mutable arrays
                -- may be accessed by pure code.
                MutArrClosure    {mccPayload = ps} -> evalAll ps
                APClosure        {fun = p, payload = ps} -> evalAll (p:ps)
                PAPClosure       {fun = p, payload = ps} -> evalAll (p:ps)
                APStackClosure   {fun = p, payload = ps} -> evalAll (p:ps)
                -- Unenterable stuff and mutable stuff
                _ -> return ()

-- make sure you free it when you're done
recordStaticObjectList :: IO (Ptr Bdescr)
recordStaticObjectList = do
    poke record_static 1
    performGC
    peek recorded_static_object_list

foreign import ccall "&record_static" record_static :: Ptr CInt
foreign import ccall "&recorded_static_object_list" recorded_static_object_list :: Ptr (Ptr Bdescr)
foreign import ccall "freeRecordedStaticObjectList" freeRecordedStaticObjectList :: IO ()
foreign import ccall "setKeepCAFs" setKeepCAFs :: IO ()

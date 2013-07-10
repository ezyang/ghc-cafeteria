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

import GHC.HeapView

import SymLookup

data Bdescr

bdescrStart, bdescrFree :: Ptr Bdescr -> IO (Ptr a)
bdescrStart = #{peek bdescr, start}
bdescrFree = #{peek bdescr, free}
bdescrLink :: Ptr Bdescr -> IO (Ptr Bdescr)
bdescrLink = #{peek bdescr, link}

{-# NOINLINE exampleCAF #-}
exampleCAF :: (Int, Int)
exampleCAF = (unsafePerformIO (putStrLn "XXX" >> return 2), 99999)

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    sol <- recordStaticObjectList
    out <- newMVar ()
    let process x@(Ptr a) = do
        case addrToAny## a of
            -- seems to go faster when you use forkIO. Probably should
            -- synchronize though
            (## v ##) -> do
                wait <- newEmptyMVar
                t <- forkIO $ staticEvaluate (Box v)
                            -- need to catch exceptions since a lot of
                            -- CAFs are things like 'error "WHOOPS"'
                            `catch` (\(SomeException _) -> return ())
                            `finally` putMVar wait ()
                _ <- forkIO $ do
                    threadDelay (10 * 1000000) -- in seconds
                    m <- tryTakeMVar wait
                    case m of
                        Nothing -> do
                            killThread t
                            sym <- lookupSymbol x
                            withMVar out . const $ case sym of
                                Nothing -> putStr ("\n" ++ show x)
                                Just s -> putStr ("\n" ++ show s)
                        Just _ -> return () -- do nothing
                readMVar wait
                withMVar out (const (putStr "."))
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
        withMVar out . const $ putStrLn ("Adding " ++ show len ++ " static objects")
        mapM_ (writeChan chan . Just) =<< peekArray len start
        next <- bdescrLink p
        when (next /= nullPtr) (go next)
    -- now do it!  it seems pretty important to not thread-bomb the system.
    let number_of_workers = 6
    waits <- replicateM number_of_workers $ do
        wait <- newEmptyMVar
        _ <- forkIO (worker >> putMVar wait ())
        return wait
    go sol
    replicateM_ number_of_workers (writeChan chan Nothing)
    mapM_ takeMVar waits
    freeRecordedStaticObjectList
    putStrLn ""
    putStrLn "------------------"
    print exampleCAF

-- We have an object which is known to be a CAF (since it came off
-- the static objects list).  How much of it do we have to evaluate?
-- Here is an important observation: any pointers contained by a CAF
-- must also be CAFs, and thus show up on the static objects list.
-- Thus, we don't need to, say, follow constructors (and indeed, we MUST
-- NOT do so, because that will lead to exponential time forcing things.)
-- So the only orders of business are to force things that need forcing,
-- and follow things that will have dynamic destinations (in particular,
-- indirections.)
staticEvaluate :: Box -> IO ()
staticEvaluate x = do
    let force = case x of Box a -> evaluate a >> primDeepEvaluate x
    closure <- getBoxedClosureData x
    case closure of
        ThunkClosure {} -> force
        SelectorClosure {} -> error "impossible"
        BlackholeClosure {} -> force
        IndClosure {indirectee = p} -> primDeepEvaluate p
        _ -> return ()

-- Like evaluate . rnf, but it requires no type class instances.
-- ToDo: We can improve this by checking if the closure in question
-- is a static one, and punting if it is.
primDeepEvaluate :: Box -> IO ()
primDeepEvaluate x = do
    let force = case x of Box a -> evaluate a >> primDeepEvaluate x
        evalAll = mapM_ primDeepEvaluate
    closure <- getBoxedClosureData x
    case tipe (info closure) of
        CONSTR_STATIC -> return ()
        CONSTR_NOCAF_STATIC -> return ()
        FUN_STATIC -> return ()
        THUNK_STATIC -> return ()
        IND_STATIC -> return ()
        _ -> case closure of
                ThunkClosure {} -> force
                SelectorClosure {} -> force
                -- forcing a blackhole causes us to WAIT for the true thread.
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

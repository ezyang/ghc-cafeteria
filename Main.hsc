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

import GHC.HeapView

import SymLookup

data Bdescr

bdescrStart, bdescrFree :: Ptr Bdescr -> IO (Ptr a)
bdescrStart = #{peek bdescr, start}
bdescrFree = #{peek bdescr, free}
bdescrLink :: Ptr Bdescr -> IO (Ptr Bdescr)
bdescrLink = #{peek bdescr, link}

number_of_workers = 1

{-# NOINLINE exampleCAF #-}
exampleCAF :: (Int, Int)
exampleCAF = (unsafePerformIO (putStrLn "XXX" >> return 2), 99999)

{-# NOINLINE out #-}
out = unsafePerformIO (newMVar ())
sync = withMVar out . const

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    putStr "Loading symbol table... "
    _ <- lookupSymbol nullPtr
    putStrLn "done."
    sol <- recordStaticObjectList
    let process x@(Ptr a) = do
        -- sym <- lookupSymbol x
        -- sync $ print sym
        -- let cond = sym == Just "rceq_closure"
        let cond = False
        case addrToAny## a of
            -- seems to go faster when you use forkIO. Probably should
            -- synchronize though
            (## v ##) -> do
                wait <- newEmptyMVar
                t <- forkIO $ staticEvaluate cond x (Box v)
                            -- need to catch exceptions since a lot of
                            -- CAFs are things like 'error "WHOOPS"'
                            `catch` (\(SomeException _) -> return ())
                            `finally` putMVar wait ()
                _ <- forkIO $ do
                    threadDelay (1 * 1000000) -- in seconds
                    m <- tryTakeMVar wait
                    case m of
                        Nothing -> do
                            killThread t
                            sym <- lookupSymbol x
                            sync $ case sym of
                                Nothing -> putStr ("\n" ++ show x)
                                Just s -> putStr ("\n" ++ show s)
                        Just _ -> return () -- do nothing
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
    -- now do it!  it seems pretty important to not thread-bomb the system.
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
staticEvaluate :: Bool -> Ptr a -> Box -> IO ()
staticEvaluate cond p x = do
    let force = do
        x' <- case x of Box a -> evaluate a
        primDeepEvaluate cond (asBox x')
    closure <- getBoxedClosureData x
    case closure of
        ThunkClosure {} -> do
            sync $ print p
            (#{poke StgIndStatic, updatable}) p (0 :: CInt)
            force
        SelectorClosure {} -> error "impossible"
        BlackholeClosure {} -> force
        IndClosure {indirectee = p} -> primDeepEvaluate cond p
        _ -> return ()

printClosure x = sync $ do
    (infotable, ws, _) <- case x of Box a -> getClosureRaw a
    Just info_name <- lookupSymbol (#{ptr StgInfoTable, code} infotable)
    -- fah bytestrings are annoying to convert to strings
    putStr ("\n" ++ show info_name ++ " " ++ intercalate " " (map (show . wordPtrToPtr . fromIntegral) (tail ws)))

-- Like evaluate . rnf, but it requires no type class instances.
-- ToDo: We can improve this by checking if the closure in question
-- is a static one, and punting if it is.
primDeepEvaluate :: Bool -> Box -> IO ()
primDeepEvaluate cond x = do
    let force = primDeepEvaluate cond . asBox =<< case x of Box a -> evaluate a
        evalAll = mapM_ (primDeepEvaluate cond)
    closure <- getBoxedClosureData x
    when cond $ printClosure x
    case tipe (info closure) of
        CONSTR_STATIC -> return ()
        CONSTR_NOCAF_STATIC -> return ()
        FUN_STATIC -> return ()
        THUNK_STATIC -> return ()
        IND_STATIC -> return ()
        _ -> case closure of
                ThunkClosure {} -> force
                SelectorClosure {} -> force
                BlackholeClosure {indirectee = p} -> force
                IndClosure {indirectee = p} -> primDeepEvaluate cond p
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

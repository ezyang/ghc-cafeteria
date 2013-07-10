module SymLookup (lookupSymbol) where

import qualified Data.IntMap.Strict as IntMap
import Data.IntMap (IntMap)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.IORef
import Foreign.Ptr
import System.IO.Unsafe
import Control.Exception

import Data.Elf
import System.Environment.Executable

{-# NOINLINE globalSymbolTable #-}
globalSymbolTable :: IORef (IntMap ByteString)
globalSymbolTable = unsafePerformIO (newIORef IntMap.empty)

processElf :: ByteString -> IntMap ByteString
processElf
  = IntMap.fromList
  . concatMap (\e -> case snd (steName e) of
      Nothing -> []
      Just v -> [(fromIntegral (steValue e), BS.copy v)])
  . concat
  . parseSymbolTables
  . parseElf

lookupSymbol :: Ptr a -> IO (Maybe ByteString)
lookupSymbol x = do
    tmp <- readIORef globalSymbolTable
    gst <- if IntMap.null tmp
              then do
                contents <- BS.readFile =<< getExecutablePath
                gst' <- evaluate (processElf contents)
                writeIORef globalSymbolTable gst'
                return gst'
              else return tmp
    return $ IntMap.lookup (fromIntegral (ptrToIntPtr x)) gst

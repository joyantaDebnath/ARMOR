{-# OPTIONS --guardedness #-}

import      Armor.Foreign.ByteString as ByteString
open import Armor.Foreign.Time
open import Armor.Prelude
import      System.Exit

module Armor.IO where

{-# FOREIGN GHC import qualified Data.ByteString as ByteString #-}
{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.IO #-}
{-# FOREIGN GHC import qualified Data.Text          #-}
{-# FOREIGN GHC import qualified Data.Text.IO as TIO #-}
{-# FOREIGN GHC import           Data.Time.Clock #-}

module Primitive where
  open import IO.Primitive
  postulate
    Handle IOMode  : Set

    readMode : IOMode
    openFile : String → IOMode → IO Handle

    getArgs : IO (List String)
    stderr  : Handle
    hPutStrLn : Handle → String → IO ⊤

    getContents    : IO ByteString.ByteString
    hGetContents   : Handle → IO ByteString.ByteString
    getCurrentTime : IO UTCTime

{-# COMPILE GHC Primitive.Handle = type System.IO.Handle #-}
{-# COMPILE GHC Primitive.IOMode = type System.IO.IOMode #-}

{-# FOREIGN GHC
aeresOpenFile :: Data.Text.Text -> System.IO.IOMode -> IO System.IO.Handle
aeresOpenFile path mode = System.IO.openFile (Data.Text.unpack path) mode
#-}

{-# COMPILE GHC Primitive.readMode = System.IO.ReadMode #-}
{-# COMPILE GHC Primitive.openFile = aeresOpenFile #-}

{-# COMPILE GHC Primitive.getArgs = fmap Data.Text.pack <$> System.Environment.getArgs #-}
{-# COMPILE GHC Primitive.stderr = System.IO.stderr #-}
{-# COMPILE GHC Primitive.hPutStrLn = TIO.hPutStrLn #-}

{-# COMPILE GHC Primitive.getContents = ByteString.getContents #-}
{-# COMPILE GHC Primitive.hGetContents = ByteString.hGetContents #-}
{-# COMPILE GHC Primitive.getCurrentTime = getCurrentTime #-}

open import IO
open System.Exit public using (exitFailure ; exitSuccess)

openFile : String → Primitive.IOMode → IO Primitive.Handle
openFile path mode = lift (Primitive.openFile path mode)

getArgs : IO (List String)
getArgs = lift Primitive.getArgs

putStrLnErr : String → IO (Level.Lift Level.zero ⊤)
putStrLnErr str = Level.lift IO.<$> (lift (Primitive.hPutStrLn Primitive.stderr str))

getByteStringContents : IO ByteString.ByteString
getByteStringContents = lift Primitive.getContents

hGetByteStringContents : Primitive.Handle → IO ByteString.ByteString
hGetByteStringContents h = lift (Primitive.hGetContents h)

getCurrentTime : IO UTCTime
getCurrentTime = lift Primitive.getCurrentTime

{-# LANGUAGE ScopedTypeVariables #-}
-- | QuickCheck smoke: happy-path ABI check + visible version pair (native FFI gate).
module Main (main) where

import Control.Monad (when)
import Data.Word (Word32)
import FFI (assertAbiCompatible, getAbiVersionPair)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)

import Test.QuickCheck (ioProperty, isSuccess, once, quickCheckResult)

main :: IO ()
main = do
  r <-
    quickCheckResult $
      once $
        ioProperty $ do
          assertAbiCompatible
          (actual, minC) <- getAbiVersionPair
          when (actual < minC) $
            error "internal: assertAbiCompatible should have rejected actual < min_compatible"
          hPutStrLn stderr $
            "UMST FFI ABI (happy path): actual="
              ++ show actual
              ++ " min_compatible="
              ++ show minC
          pure $ actual >= minC && actual == (8 :: Word32)
  if isSuccess r then exitSuccess else exitFailure

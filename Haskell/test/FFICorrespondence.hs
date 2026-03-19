-- | Runs 'FFI.runCorrespondenceTests' when the package is built with @-f with-ffi@.
-- See Docs/PROOF-REPLAY.md.
module Main (main) where

import FFI (runCorrespondenceTests)
import System.Exit (exitFailure, exitSuccess)

main :: IO ()
main = do
  ok <- runCorrespondenceTests
  if ok then exitSuccess else exitFailure

-- | Runs 'FFI.runCorrespondenceTests' when the package is built with @-f with-ffi@.
-- That suite includes 'FFI.runEtaCogCorrespondence', 'FFI.runRhoMiCorrespondence' (≥120 seeds each, |diff| ≤ 1e-9),
-- and 'FFI.runMedianConvergenceCorrespondence' (120 seeds, exact Word64) alongside gate / credit / dignity.
-- See Docs/PROOF-REPLAY.md.
module Main (main) where

import FFI (assertAbiCompatible, runCorrespondenceTests)
import System.Exit (exitFailure, exitSuccess)

main :: IO ()
main = do
  assertAbiCompatible
  ok <- runCorrespondenceTests
  if ok then exitSuccess else exitFailure

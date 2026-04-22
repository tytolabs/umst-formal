-- | Minimal executable: load @libumst_ffi@ and run `assertAbiCompatible` only (negative-test harness).
module Main (main) where

import FFI (assertAbiCompatible)

main :: IO ()
main = assertAbiCompatible

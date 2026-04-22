{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}

-- |
-- Module      : FFI
-- Description : Foreign-function interface bridging Haskell to the Rust UMST kernel
-- License     : MIT
--
-- = Architecture
--
-- The Rust kernel (@umst-core@) is compiled to a C-ABI dynamic library
-- (@libumst_ffi.dylib@ / @libumst_ffi.so@) via the @ffi-bridge/@ crate.
-- This module imports those C symbols and wraps them in safe Haskell
-- functions with proper resource management (bracket patterns) and
-- type marshalling.
--
-- The bridge exists for two reasons:
--
--   1. __Performance__: the Rust kernel is the production path; Haskell
--      calls into it for real gate evaluations.
--
--   2. __Correspondence validation__: the pure Haskell gate in "UMST"
--      and the Rust gate must agree on every input.  The property test
--      'prop_gateCorrespondence' generates random states and asserts
--      that @gateCheck old new dt == rustGateCheck old new dt@ for all
--      inputs.  Any divergence means either the Haskell model or the
--      Rust implementation has a bug — the formal layer (Agda/Coq)
--      arbitrates.
--
-- = FFI Safety
--
-- All foreign imports are declared @safe@, meaning GHC will release
-- the capability (allow other Haskell threads to run) while the
-- foreign call executes.  This is appropriate because:
--
--   * The Rust functions are pure computations (no callbacks into
--     Haskell, no GC interaction).
--   * They are fast (microseconds), so the overhead of a safe call
--     is negligible.
--   * We want the RTS to remain responsive during gate evaluation.
--
-- = Marshalling Strategy
--
-- * Primitive numerics (@Double@, @Float@, @Int32@) marshal directly.
-- * The opaque @UmstFilter@ handle is @Ptr ()@ on the Haskell side.
-- * @CThermodynamicState@ (a C struct returned by value) is handled
--   via a 'Foreign.Storable.Storable' instance and @alloca@/@peek@.
--   GHC's FFI does not support struct-by-value returns portably, so
--   we import a pointer-based shim (@umst_thermo_state_from_mix_ptr@)
--   that writes the result into caller-allocated memory.

module FFI
  ( -- * High-level wrappers
    withFilter
  , rustGateCheck
    -- * ABI gate (call before any other FFI from this process)
  , assertAbiCompatible
  , getAbiVersionPair
    -- * Property tests
  , prop_gateCorrespondence
  , runCorrespondenceTests
  , runDignityCorrespondence
  , runEtaCogCorrespondence
  , runMedianConvergenceCorrespondence
  , runOrderStatisticsCorrespondence
  , runRhoMiCorrespondence
    -- * C struct (re-exported for advanced use)
  , CThermodynamicState (..)
  ) where

import Control.Monad (when)
import Data.Word (Word32, Word64)
import Foreign
import Foreign.C.Types
import Foreign.Marshal.Array (withArray)
import Control.Exception (bracket)
import System.IO         (hPutStrLn, stderr)

import UMST

------------------------------------------------------------------------
-- Raw C Imports
------------------------------------------------------------------------

-- | Allocate a new @ThermodynamicFilter@ on the Rust heap.
-- The caller is responsible for freeing it with 'c_filter_free'.
foreign import ccall safe "umst_filter_new"
  c_filter_new :: IO (Ptr ())

-- | Free a @ThermodynamicFilter@ previously allocated by 'c_filter_new'.
-- Passing a null or already-freed pointer is undefined behaviour on the
-- Rust side; the bracket wrapper 'withFilter' prevents this.
foreign import ccall safe "umst_filter_free"
  c_filter_free :: Ptr () -> IO ()

-- | Raw gate check.  Returns 1 if the transition is admissible, 0 if
-- rejected.  The filter pointer must be valid (obtained from
-- 'c_filter_new' and not yet freed).
--
-- Parameter order matches the C header exactly:
-- @filter, old_ρ, old_ψ, old_α, old_fc, new_ρ, new_ψ, new_α, new_fc, new_fc_max, Δt@
foreign import ccall safe "umst_gate_check"
  c_gate_check
    :: Ptr ()     -- filter handle
    -> CDouble    -- old density
    -> CDouble    -- old free energy
    -> CDouble    -- old hydration
    -> CDouble    -- old strength
    -> CDouble    -- new density
    -> CDouble    -- new free energy
    -> CDouble    -- new hydration
    -> CDouble    -- new strength
    -> CDouble    -- new max strength
    -> CDouble    -- dt
    -> IO CInt

-- | Compute the internal dissipation rate \(D_{int} = -\rho\,\dot\psi\).
foreign import ccall safe "umst_dissipation"
  c_dissipation
    :: CDouble    -- old density
    -> CDouble    -- new density
    -> CDouble    -- old free energy
    -> CDouble    -- new free energy
    -> CDouble    -- dt
    -> IO CDouble

-- | Avrami–Parrott hydration-degree model.
-- Returns \(\alpha(t, T, r_{SCM})\) as a single-precision float.
foreign import ccall safe "umst_hydration_degree"
  c_hydration_degree
    :: CFloat     -- age in days
    -> CFloat     -- temperature (°C)
    -> CFloat     -- SCM replacement ratio
    -> IO CFloat

-- | Powers gel-space-ratio strength model.
-- Returns \(f_c(w/c, \alpha, a_{air}, A)\) in MPa.
foreign import ccall safe "umst_strength_powers"
  c_strength_powers
    :: CFloat     -- w/c ratio
    -> CFloat     -- degree of hydration
    -> CFloat     -- air content (fraction)
    -> CFloat     -- intrinsic strength (MPa)
    -> IO CFloat

------------------------------------------------------------------------
-- CThermodynamicState — Storable instance for struct marshalling
------------------------------------------------------------------------

-- | Haskell mirror of the C struct @CThermodynamicState@.
--
-- Layout (assuming no padding, 5 × 8 bytes = 40 bytes):
--
-- @
--   offset 0:  density          (double)
--   offset 8:  free_energy      (double)
--   offset 16: hydration_degree (double)
--   offset 24: strength         (double)
--   offset 32: max_strength     (double)
-- @
data CThermodynamicState = CThermodynamicState
  { cDensity    :: !CDouble
  , cFreeEnergy :: !CDouble
  , cHydration  :: !CDouble
  , cStrength   :: !CDouble
  , cMaxStrength :: !CDouble
  } deriving (Show, Eq)

instance Storable CThermodynamicState where
  sizeOf    _ = 5 * sizeOf (undefined :: CDouble)
  alignment _ = alignment (undefined :: CDouble)

  peek ptr = CThermodynamicState
    <$> peekElemOff (castPtr ptr) 0
    <*> peekElemOff (castPtr ptr) 1
    <*> peekElemOff (castPtr ptr) 2
    <*> peekElemOff (castPtr ptr) 3
    <*> peekElemOff (castPtr ptr) 4

  poke ptr (CThermodynamicState d fe h s ms) = do
    pokeElemOff (castPtr ptr) 0 d
    pokeElemOff (castPtr ptr) 1 fe
    pokeElemOff (castPtr ptr) 2 h
    pokeElemOff (castPtr ptr) 3 s
    pokeElemOff (castPtr ptr) 4 ms

-- | Pointer-based shim for @umst_thermo_state_from_mix@.
--
-- The C function returns a struct by value, which GHC's FFI cannot
-- portably handle.  This import expects a thin C wrapper:
--
-- @
--   void umst_thermo_state_from_mix_ptr(
--       double w_c, double alpha, double temp,
--       CThermodynamicState* out);
-- @
--
-- The wrapper is a trivial addition to @ffi-bridge/src/lib.rs@:
-- allocate the struct on the stack and copy to the out-pointer.
foreign import ccall safe "umst_thermo_state_from_mix_ptr"
  c_thermo_state_from_mix_ptr
    :: CDouble              -- w/c ratio
    -> CDouble              -- alpha
    -> CDouble              -- temperature
    -> Ptr CThermodynamicState  -- out pointer
    -> IO ()

-- | Rust C-ABI aggregate for Phase M4 (`umst_credit_greedy_sum`).
foreign import ccall unsafe "umst_credit_greedy_sum"
  c_credit_greedy_sum
    :: CSize
    -> Ptr CDouble
    -> Ptr CUChar
    -> IO CDouble

-- | Rust C-ABI dignity step (Phase N3-FPD-a, `umst_dignity_step`).
foreign import ccall unsafe "umst_dignity_step"
  c_dignity_step
    :: CDouble -> CDouble -> CDouble -> CDouble -> IO CDouble

-- | Rust C-ABI η_cog (Phase N3-FPD-b, `umst_eta_cog`).
foreign import ccall unsafe "umst_eta_cog"
  c_eta_cog
    :: CDouble -> CDouble -> CDouble -> CDouble -> IO CDouble

-- | Rust C-ABI ρ-MI bits (`umst_rho_mi_bits`, Phase FPD-RhoEstimator).
foreign import ccall unsafe "umst_rho_mi_bits"
  c_rho_mi_bits :: CDouble -> IO CDouble

-- | Theorem-derived median warmup count (`uint64_t` / `Word64`).
foreign import ccall unsafe "umst_n_warmup"
  c_n_warmup :: CDouble -> CDouble -> CDouble -> IO Word64

-- | Theorem-derived order-statistics quantile budget (`uint64_t` / `Word64`).
foreign import ccall unsafe "umst_n_quantile"
  c_n_quantile :: CDouble -> CDouble -> CDouble -> CDouble -> IO Word64

-- | Current ABI tag from the loaded @libumst_ffi@ (must be @>=@ `umst_ffi_abi_version_expected()`).
foreign import ccall unsafe "umst_ffi_abi_version"
  c_umst_ffi_abi_version :: IO CUInt

-- | Minimum ABI level this @libumst_ffi@ build supports (see @UMST_FFI_ABI_VERSION_MIN_COMPATIBLE@ in @umst_ffi.h@).
foreign import ccall unsafe "umst_ffi_abi_version_expected"
  c_umst_ffi_abi_version_expected :: IO CUInt

-- | Read @(actual, min_compatible)@ from the loaded shared library (for diagnostics / smoke tests).
getAbiVersionPair :: IO (Word32, Word32)
getAbiVersionPair = do
  a <- c_umst_ffi_abi_version
  e <- c_umst_ffi_abi_version_expected
  pure (fromIntegral a, fromIntegral e)

-- | Fail fast if @libumst_ffi@ is too old (stale @LD_LIBRARY_PATH@ / forgotten rebuild).
--
-- External callers must run this before any other FFI entry point. Semantics: require
-- @umst_ffi_abi_version() >= umst_ffi_abi_version_expected()@ from the same @.so@.
assertAbiCompatible :: IO ()
assertAbiCompatible = do
  actualW <- c_umst_ffi_abi_version
  expectedW <- c_umst_ffi_abi_version_expected
  let actual = fromIntegral actualW :: Word32
      expected = fromIntegral expectedW :: Word32
  when (actual < expected) $
    ioError $
      userError $
        "UMST FFI ABI mismatch: loaded .so reports version "
          ++ show actual
          ++ ", Haskell bindings require version >= "
          ++ show expected
          ++ ". Rebuild libumst_ffi.so with `cargo build --release -p umst-ffi --features lean-ffi` and ensure LD_LIBRARY_PATH points to the current build."

-- | Convert a C-side state to a Haskell 'ThermodynamicState'.
fromCState :: CThermodynamicState -> ThermodynamicState
fromCState cs = ThermodynamicState
  { density     = realToFrac (cDensity cs)
  , freeEnergy  = realToFrac (cFreeEnergy cs)
  , hydration   = realToFrac (cHydration cs)
  , strength    = realToFrac (cStrength cs)
  , maxStrength = realToFrac (cMaxStrength cs)
  }

------------------------------------------------------------------------
-- Safe Wrappers
------------------------------------------------------------------------

-- | Bracket pattern for filter lifecycle management.
--
-- Allocates a @ThermodynamicFilter@ on the Rust heap, passes it to
-- the callback, and guarantees deallocation even if the callback
-- throws an exception.  This is the only correct way to use the
-- filter; raw 'c_filter_new'/'c_filter_free' should not be called
-- directly.
--
-- @
--   withFilter $ \\filt -> do
--     result <- rustGateCheckWith filt oldState newState dt
--     print result
-- @
withFilter :: (Ptr () -> IO a) -> IO a
withFilter = bracket c_filter_new c_filter_free

-- | High-level gate check via the Rust FFI.
--
-- Allocates a filter, evaluates the gate, and returns a Bool.
-- The filter is freed automatically regardless of outcome.
rustGateCheck :: ThermodynamicState -> ThermodynamicState -> Double -> IO Bool
rustGateCheck old proposed dt = withFilter $ \filt -> do
  result <- c_gate_check filt
    (realToFrac $ density old)
    (realToFrac $ freeEnergy old)
    (realToFrac $ hydration old)
    (realToFrac $ strength old)
    (realToFrac $ density proposed)
    (realToFrac $ freeEnergy proposed)
    (realToFrac $ hydration proposed)
    (realToFrac $ strength proposed)
    (realToFrac $ maxStrength proposed)
    (realToFrac dt)
  pure (result == 1)

-- | Compute dissipation via the Rust kernel.
--
-- \(D_{int} = -\rho_{avg} \cdot \dot\psi\)
--
-- Returns the dissipation rate in J/(kg·s).
rustDissipation
  :: Double  -- ^ Old density
  -> Double  -- ^ New density
  -> Double  -- ^ Old free energy
  -> Double  -- ^ New free energy
  -> Double  -- ^ Δt
  -> IO Double
rustDissipation oldRho newRho oldPsi newPsi dt = do
  result <- c_dissipation
    (realToFrac oldRho)
    (realToFrac newRho)
    (realToFrac oldPsi)
    (realToFrac newPsi)
    (realToFrac dt)
  pure (realToFrac result)

-- | Compute hydration degree via the Avrami–Parrott model.
--
-- Given the age of the concrete, the curing temperature, and the SCM
-- replacement ratio, returns the degree of hydration \(\alpha\).
rustHydrationDegree
  :: Float  -- ^ Age in days
  -> Float  -- ^ Temperature (°C)
  -> Float  -- ^ SCM replacement ratio (0–1)
  -> IO Float
rustHydrationDegree ageDays tempC scmRatio = do
  result <- c_hydration_degree
    (realToFrac ageDays)
    (realToFrac tempC)
    (realToFrac scmRatio)
  pure (realToFrac result)

-- | Compute compressive strength via the Powers model.
--
-- The gel-space ratio model predicts strength from the water-cement
-- ratio, degree of hydration, air content, and intrinsic strength.
rustStrengthPowers
  :: Float  -- ^ w/c ratio
  -> Float  -- ^ Degree of hydration
  -> Float  -- ^ Air content (fraction)
  -> Float  -- ^ Intrinsic strength (MPa)
  -> IO Float
rustStrengthPowers wcRatio degHyd airContent intStr = do
  result <- c_strength_powers
    (realToFrac wcRatio)
    (realToFrac degHyd)
    (realToFrac airContent)
    (realToFrac intStr)
  pure (realToFrac result)

-- | Construct a 'ThermodynamicState' from mix parameters via the Rust kernel.
--
-- Requires the pointer-based shim (see 'c_thermo_state_from_mix_ptr').
rustFromMix :: Double -> Double -> Double -> IO ThermodynamicState
rustFromMix wc alpha temp =
  alloca $ \outPtr -> do
    c_thermo_state_from_mix_ptr
      (realToFrac wc)
      (realToFrac alpha)
      (realToFrac temp)
      outPtr
    fromCState <$> peek outPtr

------------------------------------------------------------------------
-- Property Tests
------------------------------------------------------------------------

-- | Property test: the pure Haskell gate and the Rust FFI gate must
-- agree on every input.
--
-- This function generates a single random-ish test case from the
-- given seed parameters and checks correspondence.  In production,
-- wrap this with QuickCheck's @forAll@ and an @Arbitrary@ instance
-- for 'ThermodynamicState' to get exhaustive coverage:
--
-- @
--   import Test.QuickCheck
--
--   instance Arbitrary ThermodynamicState where
--     arbitrary = ThermodynamicState
--       \<$\> choose (1800, 2600)   -- density
--       \<*\> choose (-450, 0)      -- free energy
--       \<*\> choose (0, 1)         -- hydration
--       \<*\> choose (0, 80)        -- strength
--       \<*\> choose (20, 100)      -- max strength
--
--   prop_gate :: ThermodynamicState -> ThermodynamicState -> Positive Double -> Property
--   prop_gate old new (Positive dt) = ioProperty $ prop_gateCorrespondence old new dt
-- @
--
-- The test is the keystone of the verification stack: Agda proves the
-- gate /correct/, this test proves the Rust implementation /faithful/
-- to the Haskell reference, and the Haskell reference mirrors the Agda
-- specification.  Any break in this chain is a bug.
prop_gateCorrespondence
  :: ThermodynamicState  -- ^ Old state
  -> ThermodynamicState  -- ^ Proposed state
  -> Double              -- ^ Δt (must be > 0)
  -> IO Bool
prop_gateCorrespondence old proposed dt = do
  let haskellResult = accepted (gateCheck old proposed dt)
  rustResult <- rustGateCheck old proposed dt
  let ok = haskellResult == rustResult
  if ok
    then pure True
    else do
      hPutStrLn stderr $ unlines
        [ "CORRESPONDENCE FAILURE"
        , "  old:      " ++ show old
        , "  proposed: " ++ show proposed
        , "  dt:       " ++ show dt
        , "  haskell:  " ++ show haskellResult
        , "  rust:     " ++ show rustResult
        ]
      pure False

-- | Run a batch of correspondence tests with representative states.
--
-- Covers the critical corners of the state space:
--   * Identity transition (old == new) — must always pass
--   * Forward hydration — must always pass (Theorem 1)
--   * Reverse hydration — must always fail
--   * Mass violation — must always fail
--   * Energy violation (spontaneous free-energy increase) — must always fail
runCorrespondenceTests :: IO Bool
runCorrespondenceTests = do
  let base  = fromMix 0.45 0.5 20.0
      advanced = fromMix 0.45 0.7 20.0
      badMass  = base { density = density base + 200.0 }
      badHyd   = base { hydration = hydration base - 0.1 }
      badPsi   = base { freeEnergy = freeEnergy base + 100.0 }
      dt       = 3600.0

  results <- sequence
    [ prop_gateCorrespondence base base dt
    , prop_gateCorrespondence base advanced dt
    , prop_gateCorrespondence base badMass dt
    , prop_gateCorrespondence base badHyd dt
    , prop_gateCorrespondence base badPsi dt
    ]

  creditOk <- runCreditGreedyCorrespondence
  dignityOk <- runDignityCorrespondence
  etaOk <- runEtaCogCorrespondence
  rhoOk <- runRhoMiCorrespondence
  medianOk <- runMedianConvergenceCorrespondence
  orderStatsOk <- runOrderStatisticsCorrespondence

  let gateOk = and results
      allPassed =
        gateOk
          && creditOk
          && dignityOk
          && etaOk
          && rhoOk
          && medianOk
          && orderStatsOk
  if allPassed
    then putStrLn "All correspondence tests passed."
    else
      putStrLn $
        "FAILED: "
          ++ show (length (filter not results))
          ++ " gate divergence(s); credit greedy "
          ++ if creditOk then "ok; " else "FAILED; "
          ++ "dignity step "
          ++ if dignityOk then "ok; " else "FAILED; "
          ++ "eta_cog "
          ++ if etaOk then "ok; " else "FAILED; "
          ++ "rho_mi_bits "
          ++ if rhoOk then "ok; " else "FAILED; "
          ++ "n_warmup "
          ++ if medianOk then "ok; " else "FAILED; "
          ++ "n_quantile "
          ++ if orderStatsOk then "ok." else "FAILED."
  pure allPassed

-- | Deterministic 100 seeds: Haskell filter-sum vs `umst_credit_greedy_sum`.
runCreditGreedyCorrespondence :: IO Bool
runCreditGreedyCorrespondence = go 0
 where
  go :: Int -> IO Bool
  go seed
    | seed >= 100 = pure True
    | otherwise = do
        let n = (seed * 17) `mod` 24
            idxs = [0 .. n - 1]
            ws =
              [ fromIntegral ((seed * 1103515245 + i * 12345) `mod` 100000) / 1317.0
              | i <- idxs
              ]
            bs = [ (seed + i) `mod` 3 /= 0 | i <- idxs ]
            hs = sum [ w | (w, b) <- zip ws bs, b ]
        ok <- rustCreditSum ws bs
        if abs (ok - hs) <= 1e-9 then go (seed + 1) else report seed hs ok >> pure False

  report :: Int -> Double -> Double -> IO ()
  report seed hs rv =
    hPutStrLn stderr $
      unlines
        [ "CREDIT_GREEDY_CORRESPONDENCE_FAILURE"
        , "  seed:    " ++ show seed
        , "  haskell: " ++ show hs
        , "  rust:    " ++ show rv
        ]

rustCreditSum :: [Double] -> [Bool] -> IO Double
rustCreditSum ws bs
  | length ws /= length bs =
      hPutStrLn stderr "rustCreditSum: length mismatch" >> pure (0 / 0)
  | null ws =
      pure 0.0
  | otherwise =
      let n = length ws
          flags = map (\b -> if b then 1 else 0 :: CUChar) bs
       in withArray (map realToFrac ws :: [CDouble]) $ \pw ->
            withArray flags $ \pf -> do
              r <- c_credit_greedy_sum (fromIntegral n) pw pf
              pure (realToFrac r)

-- | Pure Haskell reference for `umst_dignity_step` (must match `test/Dignity.hs`).
haskellDignityStep :: Double -> Double -> Double -> Double -> Double
haskellDignityStep tK cur mi e =
  let kb = 1.380649e-23
      lb = kb * max tK 0 * log 2
      honest = lb * mi <= e
   in if honest then min 10 (cur + mi) else cur

rustDignityStep :: Double -> Double -> Double -> Double -> IO Double
rustDignityStep tK cur mi e = do
  r <-
    c_dignity_step
      (realToFrac tK)
      (realToFrac cur)
      (realToFrac mi)
      (realToFrac e)
  pure (realToFrac r)

-- | Deterministic 120 seeds: Haskell dignity step vs `umst_dignity_step`.
runDignityCorrespondence :: IO Bool
runDignityCorrespondence = go 0
 where
  go :: Int -> IO Bool
  go seed
    | seed >= 120 = pure True
    | otherwise = do
        let tK = 200 + fromIntegral (seed `mod` 400)
            cur = fromIntegral (seed `mod` 1000) / 137.0
            mi = fromIntegral ((seed * 7) `mod` 50) / 10.0
            e = fromIntegral ((seed * 11) `mod` 8000) / 3.0
            hs = haskellDignityStep tK cur mi e
        rv <- rustDignityStep tK cur mi e
        if abs (rv - hs) <= 1e-9
          then go (seed + 1)
          else
            hPutStrLn stderr (unlines ["DIGNITY_CORRESPONDENCE_FAILURE", "  seed: " ++ show seed, "  hs: " ++ show hs, "  rust: " ++ show rv])
              >> pure False

-- | Pure Haskell reference for `umst_eta_cog` (must match `test/EtaCog.hs` `etaCog`).
haskellEtaCog :: Double -> Double -> Double -> Double -> Double
haskellEtaCog tK d mi e =
  let kb = 1.380649e-23
      lb = kb * max tK 0 * log 2
      denom = e + lb
   in if tK > 0 && d >= 0 && mi >= 0 && e >= 0 && denom > 0 then d * mi / denom else 0

rustEtaCog :: Double -> Double -> Double -> Double -> IO Double
rustEtaCog tK d mi e = do
  r <-
    c_eta_cog
      (realToFrac tK)
      (realToFrac d)
      (realToFrac mi)
      (realToFrac e)
  pure (realToFrac r)

-- | Deterministic 120 seeds: Haskell η_cog vs `umst_eta_cog`.
runEtaCogCorrespondence :: IO Bool
runEtaCogCorrespondence = go 0
 where
  go :: Int -> IO Bool
  go seed
    | seed >= 120 = pure True
    | otherwise = do
        let tK = 210 + fromIntegral (seed `mod` 390)
            d = fromIntegral (seed `mod` 900) / 120.0
            mi = fromIntegral ((seed * 5) `mod` 40) / 11.0
            e = fromIntegral ((seed * 13) `mod` 7000) / 4.0
            hs = haskellEtaCog tK d mi e
        rv <- rustEtaCog tK d mi e
        if abs (rv - hs) <= 1e-9
          then go (seed + 1)
          else
            hPutStrLn stderr (unlines ["ETA_COG_CORRESPONDENCE_FAILURE", "  seed: " ++ show seed, "  hs: " ++ show hs, "  rust: " ++ show rv])
              >> pure False

-- | Pure Haskell reference for `umst_rho_mi_bits` (must match `test/RhoEstimator.hs` `rhoMiBits`).
haskellRhoMiBits :: Double -> Double
haskellRhoMiBits rho =
  let r = max (-0.9999) (min 0.9999 rho)
      z = 1 - r * r
   in if z <= 0 then 0 else -0.5 * log z / log 2

rustRhoMiBits :: Double -> IO Double
rustRhoMiBits rho = do
  r <- c_rho_mi_bits (realToFrac rho)
  pure (realToFrac r)

-- | Deterministic 120 seeds: Haskell ρ-MI vs `umst_rho_mi_bits` (ρ ∈ [0, 0.99]).
runRhoMiCorrespondence :: IO Bool
runRhoMiCorrespondence = go 0
 where
  go :: Int -> IO Bool
  go seed
    | seed >= 120 = pure True
    | otherwise = do
        let rho =
              fromIntegral ((seed * 7919) `mod` 1000) / 1000 * 0.99
            hs = haskellRhoMiBits rho
        rv <- rustRhoMiBits rho
        if abs (rv - hs) <= 1e-9
          then go (seed + 1)
          else
            hPutStrLn stderr (unlines ["RHO_MI_CORRESPONDENCE_FAILURE", "  seed: " ++ show seed, "  rho: " ++ show rho, "  hs: " ++ show hs, "  rust: " ++ show rv])
              >> pure False

-- | Pure Haskell reference for `umst_n_warmup` (must match `test/MedianConvergence.hs`).
haskellNWarmup :: Double -> Double -> Double -> Word64
haskellNWarmup eps del rhoMn
  | eps > 0 && del > 0 && del < 1 && rhoMn > 0 =
      let b = (2 / (eps * eps * rhoMn * rhoMn)) * log (2 / del)
          n = ceiling b :: Integer
          n' = max 1 n
       in fromIntegral n'
  | otherwise = error "haskellNWarmup: invalid arguments"

rustNWarmup :: Double -> Double -> Double -> IO Word64
rustNWarmup eps del rho = do
  r <-
    c_n_warmup
      (realToFrac eps)
      (realToFrac del)
      (realToFrac rho)
  pure r

-- | Deterministic 120 seeds: Haskell `n_warmup` vs `umst_n_warmup` (exact `Word64` equality).
runMedianConvergenceCorrespondence :: IO Bool
runMedianConvergenceCorrespondence = go 0
 where
  go :: Int -> IO Bool
  go seed
    | seed >= 120 = pure True
    | otherwise = do
        let eps = 0.05 + fromIntegral (seed `mod` 50) / 100.0
            del = 0.02 + fromIntegral ((seed * 7) `mod` 70) / 100.0
            rho = 0.08 + fromIntegral ((seed * 13) `mod` 90) / 100.0
            hs = haskellNWarmup eps del rho
        rv <- rustNWarmup eps del rho
        if hs == rv
          then go (seed + 1)
          else
            hPutStrLn stderr (unlines ["N_WARMUP_CORRESPONDENCE_FAILURE", "  seed: " ++ show seed, "  eps: " ++ show eps, "  del: " ++ show del, "  rho: " ++ show rho, "  hs: " ++ show hs, "  rust: " ++ show rv])
              >> pure False

-- | Pure Haskell reference for `umst_n_quantile` (must match `test/MedianConvergence.hs` `nWarmup` when inputs are valid).
haskellNQuantile :: Double -> Double -> Double -> Double -> Word64
haskellNQuantile eps del rhoMn q
  | eps > 0 && del > 0 && del < 1 && rhoMn > 0 && q > 0 && q < 1 =
      haskellNWarmup eps del rhoMn
  | otherwise = error "haskellNQuantile: invalid arguments"

rustNQuantile :: Double -> Double -> Double -> Double -> IO Word64
rustNQuantile eps del rho q = do
  r <-
    c_n_quantile
      (realToFrac eps)
      (realToFrac del)
      (realToFrac rho)
      (realToFrac q)
  pure r

-- | Deterministic 120 seeds: Haskell `nQuantile` vs `umst_n_quantile` (exact `Word64` equality).
runOrderStatisticsCorrespondence :: IO Bool
runOrderStatisticsCorrespondence = go 0
 where
  go :: Int -> IO Bool
  go seed
    | seed >= 120 = pure True
    | otherwise = do
        let eps = 0.05 + fromIntegral (seed `mod` 50) / 100.0
            del = 0.02 + fromIntegral ((seed * 7) `mod` 70) / 100.0
            rho = 0.08 + fromIntegral ((seed * 13) `mod` 90) / 100.0
            q = 0.05 + fromIntegral ((seed * 17) `mod` 90) / 100.0
            hs = haskellNQuantile eps del rho q
        rv <- rustNQuantile eps del rho q
        if hs == rv
          then go (seed + 1)
          else
            hPutStrLn stderr (unlines ["N_QUANTILE_CORRESPONDENCE_FAILURE", "  seed: " ++ show seed, "  eps: " ++ show eps, "  del: " ++ show del, "  rho: " ++ show rho, "  q: " ++ show q, "  hs: " ++ show hs, "  rust: " ++ show rv])
              >> pure False


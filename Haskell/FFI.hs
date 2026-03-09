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
    -- * Property tests
  , prop_gateCorrespondence
  , runCorrespondenceTests
    -- * C struct (re-exported for advanced use)
  , CThermodynamicState (..)
  ) where

import Foreign
import Foreign.C.Types
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

  let allPassed = and results
  if allPassed
    then putStrLn "All correspondence tests passed."
    else putStrLn $ "FAILED: " ++ show (length (filter not results)) ++ " test(s) diverged."
  pure allPassed


-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Provenance preserved by admissible history moves; twin of Lean/Urge/ProvenancePreserve.lean,
-- Coq/UrgeProvenancePreserve.v and Agda/UrgeProvenancePreserve.agda. Provenance is a stamp chain, an admitted DAG
-- commit and a second-law witness slot. A move preserves provenance when the post chain extends the prior chain by
-- the prior commit, the DAG endpoints align with the move, the witness is retained and a held witness is the
-- admissibility of the move under the one second law.
--
-- The witness slot is a proposition in Lean, Coq and Agda; here it is a 'Bool', and implication is its Boolean form.
module UMST.UrgeProvenancePreserve
  ( Provenance (..)
  , preserves
  , postProvenance
  ) where

import UMST.UrgeAdmitKleisli

-- | Typed provenance: stamp chain, admitted DAG commit and second-law witness slot.
data Provenance = Provenance { ucrsChain :: [Int], dagCommit :: Int, landauerWitness :: Bool }
  deriving (Eq, Show)

-- | Preservation: the post extends the stamp chain, aligns the DAG endpoints, retains the witness.
preserves :: HistoryTransition -> Provenance -> Provenance -> Bool
preserves t prior post =
  dagCommit prior == commitId (priorSnapshot t)
    && dagCommit post == commitId (postSnapshot t)
    && ucrsChain post == ucrsChain prior ++ [dagCommit prior]
    && (not (landauerWitness prior) || landauerWitness post)
    && (not (landauerWitness post) || admissibleHistoryTransition t)

-- | The provenance after a move: the stamp chain extended by the prior commit, the DAG at the move's target.
postProvenance :: HistoryTransition -> Provenance -> Provenance
postProvenance t prior = Provenance (ucrsChain prior ++ [dagCommit prior]) (commitId (postSnapshot t)) True

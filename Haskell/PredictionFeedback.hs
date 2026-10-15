-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: Apache-2.0
-- |
-- A prediction-then-observation turn of the learning loop as a measureFeedback instance of the one predicate;
-- twin of Lean/PredictionFeedback.lean, Coq/PredictionFeedback.v and Agda/PredictionFeedback.agda, on exact
-- rationals (the mutual information in nats carried as data, as in Agda). test/PredictionFeedbackProps.hs decides
-- the statements on random turns.
module PredictionFeedback
  ( Turn (..)
  , turnAdmissible
  , against
  , gatedError
  ) where

-- | One turn: extracted work, free-energy change, k_B T of the bath, and the information between prediction and
-- outcome.
data Turn = Turn { turnWork :: Rational, turnDeltaF :: Rational, turnKBT :: Rational, turnInfo :: Rational }
  deriving (Eq, Show)

-- | The Sagawa–Ueda inequality of the measureFeedback case: W_ext <= -dF + k_B T I.
turnAdmissible :: Turn -> Bool
turnAdmissible t = turnWork t <= negate (turnDeltaF t) + turnKBT t * turnInfo t

-- | The same turn judged against another information (the receipts', or a summary's).
against :: Turn -> Rational -> Turn
against t i = t { turnInfo = i }

-- | The error of a choice from the outcome.
gatedError :: Rational -> Rational -> Rational
gatedError choice outcome = abs (choice - outcome)

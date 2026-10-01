-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
-- |
-- Properties of "UMST.CoordinationContract": the four laws proved in Lean, Coq and Agda, and the runtime-model
-- properties umst-ucrs tested before its proofs moved here. Each law quantifies over a nonnegative bit energy.
module CoordinationContractProps where

import Test.QuickCheck
import UMST.CoordinationContract

nonneg :: Gen Rational
nonneg = abs <$> arbitrary

prop_cost_nonneg :: Property
prop_cost_nonneg = forAll nonneg $ \e -> forAll nonneg $ \bits -> cost e bits >= 0

prop_cost_additive :: Property
prop_cost_additive = forAll nonneg $ \e -> \a b -> cost e (a + b) == cost e a + cost e b

-- The state is built inside admission (budget and desync = cost + slack); a random state rarely is.
admitted :: Gen (Rational, Rational, ClockThermState)
admitted = do
  e <- nonneg
  bits <- nonneg
  sb <- nonneg
  sd <- nonneg
  spent <- nonneg
  pure (e, bits, ClockThermState (cost e bits + sd) (cost e bits + sb) spent)

prop_admitted_cost_bounded :: Property
prop_admitted_cost_bounded = forAll admitted $ \(e, bits, s) ->
  admits e s bits && cost e bits >= 0 && cost e bits <= budget s && cost e bits <= desyncEnergy s && budget s >= 0

prop_gatedSync_second_law :: Property
prop_gatedSync_second_law = forAll admitted $ \(e, bits, s) ->
  let s' = gatedSync e s bits
   in desyncEnergy s' <= desyncEnergy s && totalSyncCost s <= totalSyncCost s'

prop_clockRun_monotone :: Property
prop_clockRun_monotone =
  forAll (listOf nonneg) $ \ds -> \t d ->
    let c = ClockState t d
        c' = clockRun c ds
     in drift c' >= drift c && tick c' == tick c + length ds

genParticipant :: Gen Participant
genParticipant = Participant <$> arbitrary <*> arbitrary <*> arbitrary

prop_honestCredits_append_faulty :: Property
prop_honestCredits_append_faulty =
  forAll (listOf genParticipant) $ \ps -> forAll (listOf genParticipant) $ \fs ->
    let faultyCohort = map (\p -> p {faulty = True}) fs
     in honestCredits (ps ++ faultyCohort) == honestCredits ps

prop_wireIter_seq :: Property
prop_wireIter_seq = forAll (choose (0, 200)) $ \n -> \m ->
  wireSeq (wireIter n (WireStamp m)) == m + fromIntegral n

genPeer :: Gen PeerCredit
genPeer = PeerCredit <$> arbitrary <*> arbitrary <*> (abs <$> arbitrary) <*> pure 0

prop_bestPeer_highest_healthy_credit :: Property
prop_bestPeer_highest_healthy_credit = forAll (listOf genPeer) $ \peers ->
  let healthy = filter ((> 1 / 10) . accuracyScore) peers
   in case bestPeer peers of
        Nothing -> null healthy
        Just pid -> any (\p -> peerId p == pid && all (\q -> creditBits p >= creditBits q) healthy) healthy

prop_failed_sync_drops_credit :: Property
prop_failed_sync_drops_credit = forAll genPeer $ \p -> forAll (abs <$> arbitrary `suchThat` (> 0)) $ \bits ->
  let up = recordSync p bits True
   in creditBits (recordSync up bits False) < creditBits up

prop_gate_rejects_over_budget :: Property
prop_gate_rejects_over_budget =
  forAll (abs <$> arbitrary `suchThat` (> 0)) $ \e -> forAll nonneg $ \budgetBits -> forAll nonneg $ \extra ->
    let s = ClockThermState (cost e (budgetBits + extra)) (cost e budgetBits) 0
     in extra > 0 ==> not (admits e s (budgetBits + extra))

prop_cost_monotone_in_bits :: Property
prop_cost_monotone_in_bits = forAll nonneg $ \e -> forAll nonneg $ \a -> forAll nonneg $ \b ->
  cost e (min a b) <= cost e (max a b)

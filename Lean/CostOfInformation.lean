-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: CostOfInformation.lean

  The cost of information, composed over the one predicate `UMST.ProcessFamily.SecondLaw`:

  * an erasure that obeys the predicate removes at most 1/(k_B T) nats of entropy per joule of the work it
    dissipates (`informationPerJoule_le`);
  * erasing b bits (the uniform distribution on 2^b states, to a point) costs at least b · k_B T ln 2 joules
    (`bitErasure_cost`), since the uniform distribution on n states carries ln n nats (`shannonEntropy_uniform`);
  * a cockpit claim whose energy is the work of such an erasure spends honestly (`honest_spend_of_secondLaw`), and
    an honest claim's information-per-joule score is at most its dignity over the Landauer bit energy
    (`eta_cog_le_of_honest`, `eta_cog_le_of_secondLaw`): the metric is bounded by the second law.

  Work in the erase instance is in units of k_B times kelvin; in joules it is k_B · W (`SecondLaw_transformation_iff_SI`).
-/

import Process
import EtaCog
import Constants.SIBridge

open Real Finset UMST.LandauerLaw UMST.ProcessFamily UMST.Formal.Dignity UMST.Formal.EtaCog

namespace UMST.CostOfInformation

/-- The uniform distribution on `n` states carries `ln n` nats. -/
theorem shannonEntropy_uniform (n : ℕ) (hn : 0 < n) : shannonEntropy (uniformDist n hn) = log n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  simp only [shannonEntropy, uniformDist, Finset.sum_const, card_fin, nsmul_eq_mul]
  rw [one_div, Real.log_inv]
  field_simp

/-- In joules: an erasure obeying the predicate dissipates at least k_B T times the entropy it removes. -/
theorem entropyDrop_joules_le (b : HeatBath) (W : ℝ) {n : ℕ} (p q : ProbDist n)
    (h : SecondLaw (.erase ⟨b, W⟩) (.transformation p q)) :
    kB * b.bathTemp.val * (shannonEntropy p - shannonEntropy q) ≤ kB * W := by
  have hT := b.bathTemp.property
  have h' : shannonEntropy p - shannonEntropy q ≤ W / b.bathTemp.val := h
  rw [le_div_iff₀ hT] at h'
  nlinarith [kB_pos]

/-- **Information per joule**: an erasure obeying the predicate removes at most 1/(k_B T) nats per joule. -/
theorem informationPerJoule_le (b : HeatBath) (W : ℝ) (hW : 0 < W) {n : ℕ} (p q : ProbDist n)
    (h : SecondLaw (.erase ⟨b, W⟩) (.transformation p q)) :
    (shannonEntropy p - shannonEntropy q) / (kB * W) ≤ 1 / (kB * b.bathTemp.val) := by
  have hT := b.bathTemp.property
  have hkW : 0 < kB * W := mul_pos kB_pos hW
  have hkT : 0 < kB * b.bathTemp.val := mul_pos kB_pos hT
  rw [div_le_div_iff₀ hkW hkT]
  have := entropyDrop_joules_le b W p q h
  nlinarith

/-- **The cost of b bits**: erasing the uniform distribution on 2^b states to a point costs at least
    b · k_B T ln 2 joules. -/
theorem bitErasure_cost (b : HeatBath) (W : ℝ) (bits : ℕ)
    (h : SecondLaw (.erase ⟨b, W⟩)
      (.transformation (uniformDist (2 ^ bits) (pow_pos two_pos bits)) (diracDist (0 : Fin (2 ^ bits))))) :
    bits * (kB * b.bathTemp.val * log 2) ≤ kB * W := by
  have hc := entropyDrop_joules_le b W _ _ h
  rw [shannonEntropy_uniform, diracEntropy_zero (pow_pos two_pos bits), Nat.cast_pow, Real.log_pow] at hc
  push_cast at hc
  nlinarith

/-- The cockpit's Landauer bit energy is k_B T ln 2 with the predicate's k_B. -/
lemma landauer_joules_per_bit_eq (T : ℝ) : landauer_joules_per_bit T = kB * T * log 2 := by
  unfold landauer_joules_per_bit landauerBitEnergy
  rw [UMST.Constants.SIBridge.kBoltzmannSI_eq, ← UMST.Constants.SIBridge.landauerLaw_kB_eq]

/-- **Honest spend from the second law**: a claim of b bits whose energy is the work, in joules, of an erasure of
    b bits that obeys the predicate pays the Landauer floor. -/
theorem honest_spend_of_secondLaw (b : HeatBath) (W : ℝ) (bits : ℕ) (c : DignityClaim)
    (hbits : c.delta_mi_bits = bits) (hE : c.delta_energy_j = kB * W)
    (h : SecondLaw (.erase ⟨b, W⟩)
      (.transformation (uniformDist (2 ^ bits) (pow_pos two_pos bits)) (diracDist (0 : Fin (2 ^ bits))))) :
    honest_spend b.bathTemp.val c := by
  unfold honest_spend
  rw [landauer_joules_per_bit_eq, hbits, hE]
  have := bitErasure_cost b W bits h
  linarith

/-- **η_cog is bounded by the Landauer floor**: an honest claim scores at most its dignity over k_B T ln 2. -/
theorem eta_cog_le_of_honest (d : Dignity) (c : EtaCogClaim)
    (h : landauer_joules_per_bit c.T * c.delta_mi_bits ≤ c.delta_energy_j) :
    eta_cog d c ≤ d.value / landauer_joules_per_bit c.T := by
  have hL : 0 < landauer_joules_per_bit c.T := landauer_joules_per_bit_pos c.hT
  have hD : 0 < etaDenom c := etaDenom_pos c
  unfold eta_cog
  rw [div_le_div_iff₀ hD hL]
  unfold etaDenom
  have hd : 0 ≤ d.value := d.nonneg
  nlinarith [mul_le_mul_of_nonneg_left h hd, mul_nonneg hd hL.le]

/-- The bound composed over the predicate: a claim of b bits paid by an erasure obeying the second law at the
    claim's temperature scores at most its dignity over k_B T ln 2. -/
theorem eta_cog_le_of_secondLaw (d : Dignity) (c : EtaCogClaim) (b : HeatBath) (W : ℝ) (bits : ℕ)
    (hT : b.bathTemp.val = c.T) (hbits : c.delta_mi_bits = bits) (hE : c.delta_energy_j = kB * W)
    (h : SecondLaw (.erase ⟨b, W⟩)
      (.transformation (uniformDist (2 ^ bits) (pow_pos two_pos bits)) (diracDist (0 : Fin (2 ^ bits))))) :
    eta_cog d c ≤ d.value / landauer_joules_per_bit c.T := by
  apply eta_cog_le_of_honest
  rw [landauer_joules_per_bit_eq, hbits, hE, ← hT]
  have := bitErasure_cost b W bits h
  linarith

end UMST.CostOfInformation

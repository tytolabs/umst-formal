-- SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
-- SPDX-License-Identifier: MIT
/-
  UMST-Formal: ShrinkageB4.lean — B2 shrinkage envelope + development scaffold.
  G75-L02: `shrinkageDevelopmentExp` mirrors Rust `1 - exp(-3α/α_ult)` on ℝ.
  Zero sorry. Not cert Proved — CC-P-B2-1 operator-gated.
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace UMST

open Rat

def criticalWcChemPin : ℚ := 42 / 100
def b4WcLo : ℚ := 30 / 100
def b4WcMid : ℚ := 50 / 100
def b4WcHi : ℚ := 60 / 100

lemma criticalWcChemPin_pos : 0 < criticalWcChemPin := by norm_num [criticalWcChemPin]
lemma b4WcMid_le_hi : b4WcMid ≤ b4WcHi := by norm_num [b4WcMid, b4WcHi]
lemma b4WcLo_lt_critical : b4WcLo < criticalWcChemPin := by norm_num [b4WcLo, criticalWcChemPin]
lemma b4WcLo_le_critical : b4WcLo ≤ criticalWcChemPin := le_of_lt b4WcLo_lt_critical
lemma critical_le_b4WcMid : criticalWcChemPin ≤ b4WcMid := by norm_num [criticalWcChemPin, b4WcMid]
lemma b4WcLo_lt_mid : b4WcLo < b4WcMid := by norm_num [b4WcLo, b4WcMid]
lemma critical_lt_mid : criticalWcChemPin < b4WcMid := by norm_num [criticalWcChemPin, b4WcMid]
lemma b4WcLo_lt_hi : b4WcLo < b4WcHi := by norm_num [b4WcLo, b4WcHi]
lemma b4WcMid_lt_hi : b4WcMid < b4WcHi := by norm_num [b4WcMid, b4WcHi]

def b4WcAdmissible (wc : ℚ) : Prop := 0 ≤ wc ∧ wc ≤ b4WcHi

noncomputable def b4UltimateEnvelope (wc : ℚ) : ℚ :=
  if wc ≤ b4WcLo then
    -1000 - 500 * (b4WcLo - wc) / (5 / 100)
  else if wc ≤ criticalWcChemPin then
    -600 - 400 * (criticalWcChemPin - wc) / (12 / 100)
  else if wc ≤ b4WcMid then
    -200 - 400 * (b4WcMid - wc) / (8 / 100)
  else
    -100 * max (b4WcHi - wc) 0 / (10 / 100)

private lemma b4UltimateEnvelope_nonpos_branch_lo {wc : ℚ} (h : wc ≤ b4WcLo) :
    b4UltimateEnvelope wc ≤ 0 := by
  unfold b4UltimateEnvelope; simp only [h, le_refl, if_true, if_pos]
  have hden : 0 < (5 / 100 : ℚ) := by norm_num
  have hnum : 0 ≤ b4WcLo - wc := sub_nonneg.mpr h
  have hsub : 500 * (b4WcLo - wc) / (5 / 100) ≥ 0 :=
    div_nonneg (mul_nonneg (by norm_num) hnum) (le_of_lt hden)
  linarith

private lemma b4UltimateEnvelope_nonpos_branch_critical {wc : ℚ}
    (hlo : b4WcLo < wc) (h : wc ≤ criticalWcChemPin) :
    b4UltimateEnvelope wc ≤ 0 := by
  unfold b4UltimateEnvelope
  simp only [not_le.mpr hlo, h, le_refl, if_false, if_true, if_pos]
  have hden : 0 < (12 / 100 : ℚ) := by norm_num
  have hnum : 0 ≤ criticalWcChemPin - wc := sub_nonneg.mpr h
  have hsub : 400 * (criticalWcChemPin - wc) / (12 / 100) ≥ 0 :=
    div_nonneg (mul_nonneg (by norm_num) hnum) (le_of_lt hden)
  linarith

private lemma b4UltimateEnvelope_nonpos_branch_mid {wc : ℚ}
    (hcrit : criticalWcChemPin < wc) (h : wc ≤ b4WcMid) :
    b4UltimateEnvelope wc ≤ 0 := by
  unfold b4UltimateEnvelope
  simp only [not_le.mpr (lt_of_le_of_lt b4WcLo_le_critical hcrit), not_le.mpr hcrit, h, le_refl,
    if_false, if_true, if_pos]
  have hden : 0 < (8 / 100 : ℚ) := by norm_num
  have hnum : 0 ≤ b4WcMid - wc := sub_nonneg.mpr h
  have hsub : 400 * (b4WcMid - wc) / (8 / 100) ≥ 0 :=
    div_nonneg (mul_nonneg (by norm_num) hnum) (le_of_lt hden)
  linarith

private lemma b4UltimateEnvelope_nonpos_branch_hi {wc : ℚ} (h : b4WcMid < wc) :
    b4UltimateEnvelope wc ≤ 0 := by
  unfold b4UltimateEnvelope
  simp only [not_le.mpr (lt_trans b4WcLo_lt_mid h), not_le.mpr (lt_trans critical_lt_mid h),
    not_le.mpr h, if_false]
  have hmax : 0 ≤ max (b4WcHi - wc) 0 := le_max_right _ _
  have hden : 0 < (10 / 100 : ℚ) := by norm_num
  have hsub : 100 * max (b4WcHi - wc) 0 / (10 / 100) ≥ 0 :=
    div_nonneg (mul_nonneg (by norm_num) hmax) (le_of_lt hden)
  linarith

theorem b4UltimateEnvelope_nonpos {wc : ℚ} (hwc : b4WcAdmissible wc) :
    b4UltimateEnvelope wc ≤ 0 := by
  rcases hwc with ⟨_, _⟩
  by_cases hlo : wc ≤ b4WcLo
  · exact b4UltimateEnvelope_nonpos_branch_lo hlo
  · by_cases hcrit : wc ≤ criticalWcChemPin
    · exact b4UltimateEnvelope_nonpos_branch_critical (lt_of_not_ge hlo) hcrit
    · by_cases hmid : wc ≤ b4WcMid
      · exact b4UltimateEnvelope_nonpos_branch_mid (lt_of_not_ge hcrit) hmid
      · exact b4UltimateEnvelope_nonpos_branch_hi (lt_of_not_ge hmid)

theorem b4UltimateEnvelope_at_hi : b4UltimateEnvelope b4WcHi = 0 := by
  unfold b4UltimateEnvelope b4WcHi b4WcLo criticalWcChemPin b4WcMid; norm_num

theorem b4UltimateEnvelope_at_lo : b4UltimateEnvelope b4WcLo = -1000 := by
  unfold b4UltimateEnvelope b4WcLo b4WcHi criticalWcChemPin b4WcMid; norm_num

theorem b4UltimateEnvelope_at_critical : b4UltimateEnvelope criticalWcChemPin = -600 := by
  unfold b4UltimateEnvelope criticalWcChemPin b4WcLo b4WcHi b4WcMid; norm_num

theorem b4UltimateEnvelope_at_mid : b4UltimateEnvelope b4WcMid = -200 := by
  unfold b4UltimateEnvelope b4WcMid b4WcLo criticalWcChemPin b4WcHi; norm_num

private lemma b4UltimateEnvelope_mono_branch_lo {wc₁ wc₂ : ℚ}
    (hlo₁ : wc₁ ≤ b4WcLo) (hlo₂ : wc₂ ≤ b4WcLo) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ := by
  unfold b4UltimateEnvelope; simp only [hlo₁, hlo₂, le_refl, if_true, if_pos]; linarith

private lemma b4UltimateEnvelope_mono_branch_critical {wc₁ wc₂ : ℚ}
    (hlo₁ : b4WcLo < wc₁) (hlo₂ : b4WcLo < wc₂) (hcrit₁ : wc₁ ≤ criticalWcChemPin)
    (hcrit₂ : wc₂ ≤ criticalWcChemPin) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ := by
  unfold b4UltimateEnvelope
  simp only [not_le.mpr hlo₁, not_le.mpr hlo₂, hcrit₁, hcrit₂, le_refl, if_false, if_true, if_pos]
  linarith

private lemma b4UltimateEnvelope_mono_branch_mid {wc₁ wc₂ : ℚ}
    (hcrit₁ : criticalWcChemPin < wc₁) (hcrit₂ : criticalWcChemPin < wc₂)
    (hmid₁ : wc₁ ≤ b4WcMid) (hmid₂ : wc₂ ≤ b4WcMid) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ := by
  unfold b4UltimateEnvelope
  simp only [not_le.mpr (lt_trans b4WcLo_lt_critical hcrit₁), not_le.mpr (lt_trans b4WcLo_lt_critical hcrit₂),
    not_le.mpr hcrit₁, not_le.mpr hcrit₂, hmid₁, hmid₂, le_refl, if_false, if_true, if_pos]
  linarith

private lemma b4UltimateEnvelope_mono_branch_hi {wc₁ wc₂ : ℚ}
    (hmid₁ : b4WcMid < wc₁) (hmid₂ : b4WcMid < wc₂) (_hhi₁ : wc₁ ≤ b4WcHi) (_hhi₂ : wc₂ ≤ b4WcHi)
    (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ := by
  unfold b4UltimateEnvelope
  simp only [not_le.mpr (lt_trans b4WcLo_lt_mid hmid₁), not_le.mpr (lt_trans b4WcLo_lt_mid hmid₂),
    not_le.mpr (lt_trans critical_lt_mid hmid₁), not_le.mpr (lt_trans critical_lt_mid hmid₂),
    not_le.mpr hmid₁, not_le.mpr hmid₂, if_false]
  have hmax : max (b4WcHi - wc₂) 0 ≤ max (b4WcHi - wc₁) 0 := by
    rcases le_total (b4WcHi - wc₂) 0 with h₂ | h₂
    · rcases le_total (b4WcHi - wc₁) 0 with h₁ | h₁ <;> simp [h₂, h₁]
    · simp [h₂, sub_le_sub_left h _]
  linarith

theorem b4UltimateEnvelope_mono_on_lo {wc₁ wc₂ : ℚ}
    (hlo₁ : wc₁ ≤ b4WcLo) (hlo₂ : wc₂ ≤ b4WcLo) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ :=
  b4UltimateEnvelope_mono_branch_lo hlo₁ hlo₂ h

theorem b4UltimateEnvelope_mono_on_critical {wc₁ wc₂ : ℚ}
    (hlo₁ : b4WcLo < wc₁) (hlo₂ : b4WcLo < wc₂) (hcrit₁ : wc₁ ≤ criticalWcChemPin)
    (hcrit₂ : wc₂ ≤ criticalWcChemPin) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ :=
  b4UltimateEnvelope_mono_branch_critical hlo₁ hlo₂ hcrit₁ hcrit₂ h

theorem b4UltimateEnvelope_mono_on_mid {wc₁ wc₂ : ℚ}
    (hcrit₁ : criticalWcChemPin < wc₁) (hcrit₂ : criticalWcChemPin < wc₂)
    (hmid₁ : wc₁ ≤ b4WcMid) (hmid₂ : wc₂ ≤ b4WcMid) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ :=
  b4UltimateEnvelope_mono_branch_mid hcrit₁ hcrit₂ hmid₁ hmid₂ h

theorem b4UltimateEnvelope_mono_on_hi {wc₁ wc₂ : ℚ}
    (hmid₁ : b4WcMid < wc₁) (hmid₂ : b4WcMid < wc₂) (hhi₁ : wc₁ ≤ b4WcHi) (hhi₂ : wc₂ ≤ b4WcHi)
    (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ :=
  b4UltimateEnvelope_mono_branch_hi hmid₁ hmid₂ hhi₁ hhi₂ h

theorem b4UltimateEnvelope_mid_knot_le_hi_branch :
    b4UltimateEnvelope b4WcMid ≤ -100 := by
  rw [b4UltimateEnvelope_at_mid]; norm_num

theorem b4UltimateEnvelope_knots_mono_lo_critical :
    b4UltimateEnvelope b4WcLo ≤ b4UltimateEnvelope criticalWcChemPin := by
  rw [b4UltimateEnvelope_at_lo, b4UltimateEnvelope_at_critical]; norm_num

theorem b4UltimateEnvelope_knots_mono_critical_mid :
    b4UltimateEnvelope criticalWcChemPin ≤ b4UltimateEnvelope b4WcMid := by
  rw [b4UltimateEnvelope_at_critical, b4UltimateEnvelope_at_mid]; norm_num

theorem b4UltimateEnvelope_knots_mono_mid_hi :
    b4UltimateEnvelope b4WcMid ≤ b4UltimateEnvelope b4WcHi := by
  rw [b4UltimateEnvelope_at_mid, b4UltimateEnvelope_at_hi]; norm_num

theorem b4UltimateEnvelope_knots_mono :
    b4UltimateEnvelope b4WcLo ≤ b4UltimateEnvelope criticalWcChemPin ∧
      b4UltimateEnvelope criticalWcChemPin ≤ b4UltimateEnvelope b4WcMid ∧
        b4UltimateEnvelope b4WcMid ≤ b4UltimateEnvelope b4WcHi :=
  ⟨b4UltimateEnvelope_knots_mono_lo_critical, b4UltimateEnvelope_knots_mono_critical_mid,
    b4UltimateEnvelope_knots_mono_mid_hi⟩

private lemma b4UltimateEnvelope_mono_from_lo_knot {wc : ℚ}
    (hlo : b4WcLo ≤ wc) (hcrit : wc ≤ criticalWcChemPin) :
    b4UltimateEnvelope b4WcLo ≤ b4UltimateEnvelope wc := by
  rcases le_iff_eq_or_lt.mp hlo with rfl | hlt
  · exact le_refl _
  · rcases le_iff_eq_or_lt.mp hcrit with rfl | _
    · exact b4UltimateEnvelope_knots_mono_lo_critical
    · have hdiff : criticalWcChemPin - wc ≤ 12 / 100 := by
        have hpin : criticalWcChemPin - b4WcLo = 12 / 100 := by norm_num [criticalWcChemPin, b4WcLo]
        linarith [le_of_lt hlt, hpin]
      have hterm : 400 * (criticalWcChemPin - wc) / (12 / 100) ≤ 400 := by
        rw [div_le_iff (by norm_num : (0 : ℚ) < 12 / 100)]
        nlinarith
      calc
        b4UltimateEnvelope b4WcLo = -1000 := b4UltimateEnvelope_at_lo
        _ ≤ -600 - 400 * (criticalWcChemPin - wc) / (12 / 100) := by linarith
        _ = b4UltimateEnvelope wc := by
          unfold b4UltimateEnvelope
          simp only [not_le.mpr hlt, hcrit, le_refl, if_false, if_true, if_pos]

private lemma b4UltimateEnvelope_mono_from_critical_knot {wc : ℚ}
    (hcrit : criticalWcChemPin ≤ wc) (hmid : wc ≤ b4WcMid) :
    b4UltimateEnvelope criticalWcChemPin ≤ b4UltimateEnvelope wc := by
  rcases le_iff_eq_or_lt.mp hcrit with rfl | hlt
  · exact le_refl _
  · rcases le_iff_eq_or_lt.mp hmid with rfl | _
    · exact b4UltimateEnvelope_knots_mono_critical_mid
    · have hdiff : b4WcMid - wc ≤ 8 / 100 := by
        have hpin : b4WcMid - criticalWcChemPin = 8 / 100 := by norm_num [b4WcMid, criticalWcChemPin]
        linarith [le_of_lt hlt, hpin]
      have hterm : 400 * (b4WcMid - wc) / (8 / 100) ≤ 400 := by
        rw [div_le_iff (by norm_num : (0 : ℚ) < 8 / 100)]
        nlinarith
      calc
        b4UltimateEnvelope criticalWcChemPin = -600 := b4UltimateEnvelope_at_critical
        _ ≤ -200 - 400 * (b4WcMid - wc) / (8 / 100) := by linarith
        _ = b4UltimateEnvelope wc := by
          unfold b4UltimateEnvelope
          simp only [not_le.mpr (lt_trans b4WcLo_lt_critical hlt), not_le.mpr hlt, hmid, le_refl,
            if_false, if_true, if_pos]

private lemma b4UltimateEnvelope_mono_from_mid_knot {wc : ℚ}
    (hmid : b4WcMid ≤ wc) (hhi : wc ≤ b4WcHi) :
    b4UltimateEnvelope b4WcMid ≤ b4UltimateEnvelope wc := by
  rcases le_iff_eq_or_lt.mp hmid with rfl | hlt
  · exact le_refl _
  · rcases le_iff_eq_or_lt.mp hhi with rfl | _
    · exact b4UltimateEnvelope_knots_mono_mid_hi
    · have hbound : b4WcHi - wc ≤ 10 / 100 := by
        have hpin : b4WcHi - b4WcMid = 10 / 100 := by norm_num [b4WcHi, b4WcMid]
        linarith [le_of_lt hlt, hpin]
      have hterm : 100 * (b4WcHi - wc) / (10 / 100) ≤ 100 := by
        rw [div_le_iff (by norm_num : (0 : ℚ) < 10 / 100)]
        nlinarith
      calc
        b4UltimateEnvelope b4WcMid = -200 := b4UltimateEnvelope_at_mid
        _ ≤ -100 * max (b4WcHi - wc) 0 / (10 / 100) := by
          have hpos : 0 ≤ b4WcHi - wc := sub_nonneg.mpr hhi
          have hmax : max (b4WcHi - wc) 0 = b4WcHi - wc := max_eq_left hpos
          rw [hmax]; linarith
        _ = b4UltimateEnvelope wc := by
          unfold b4UltimateEnvelope
          simp only [not_le.mpr (lt_trans b4WcLo_lt_mid hlt), not_le.mpr (lt_trans critical_lt_mid hlt),
            not_le.mpr hlt, if_false]

private lemma b4UltimateEnvelope_mono_on_critical_closed {wc₁ wc₂ : ℚ}
    (hlo₁ : b4WcLo ≤ wc₁) (hcrit₁ : wc₁ ≤ criticalWcChemPin)
    (hlo₂ : b4WcLo ≤ wc₂) (hcrit₂ : wc₂ ≤ criticalWcChemPin) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ := by
  rcases le_iff_eq_or_lt.mp hlo₁ with h₁eq | h₁lt
  · rcases le_iff_eq_or_lt.mp hlo₂ with h₂eq | h₂lt
    · subst h₁eq; subst h₂eq; exact le_refl _
    · subst h₁eq
      rcases le_iff_eq_or_lt.mp hcrit₂ with h₂crit_eq | hcrit₂lt
      · subst h₂crit_eq; exact b4UltimateEnvelope_knots_mono_lo_critical
      · exact b4UltimateEnvelope_mono_from_lo_knot hlo₂ hcrit₂
  · rcases le_iff_eq_or_lt.mp hlo₂ with h₂eq | h₂lt
    · linarith [h₁lt, h₂eq]
    · exact b4UltimateEnvelope_mono_on_critical h₁lt h₂lt hcrit₁ hcrit₂ h

private lemma b4UltimateEnvelope_mono_on_mid_closed {wc₁ wc₂ : ℚ}
    (hcrit₁ : criticalWcChemPin ≤ wc₁) (hmid₁ : wc₁ ≤ b4WcMid)
    (hcrit₂ : criticalWcChemPin ≤ wc₂) (hmid₂ : wc₂ ≤ b4WcMid) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ := by
  rcases le_iff_eq_or_lt.mp hcrit₁ with h₁eq | h₁lt
  · rcases le_iff_eq_or_lt.mp hcrit₂ with h₂eq | h₂lt
    · subst h₁eq; subst h₂eq; exact le_refl _
    · subst h₁eq
      rcases le_iff_eq_or_lt.mp hmid₂ with h₂mid_eq | hmid₂lt
      · subst h₂mid_eq; exact b4UltimateEnvelope_knots_mono_critical_mid
      · exact b4UltimateEnvelope_mono_from_critical_knot (le_of_lt h₂lt) hmid₂
  · rcases le_iff_eq_or_lt.mp hcrit₂ with h₂eq | h₂lt
    · linarith [h₁lt, h₂eq]
    · exact b4UltimateEnvelope_mono_on_mid h₁lt h₂lt hmid₁ hmid₂ h

private lemma b4UltimateEnvelope_mono_on_hi_closed {wc₁ wc₂ : ℚ}
    (hmid₁ : b4WcMid ≤ wc₁) (hhi₁ : wc₁ ≤ b4WcHi)
    (hmid₂ : b4WcMid ≤ wc₂) (hhi₂ : wc₂ ≤ b4WcHi) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ := by
  rcases le_iff_eq_or_lt.mp hmid₁ with h₁eq | h₁lt
  · rcases le_iff_eq_or_lt.mp hmid₂ with h₂eq | h₂lt
    · subst h₁eq; subst h₂eq; exact le_refl _
    · subst h₁eq
      rcases le_iff_eq_or_lt.mp hhi₂ with h₂hi_eq | _
      · subst h₂hi_eq; exact b4UltimateEnvelope_knots_mono_mid_hi
      · exact b4UltimateEnvelope_mono_from_mid_knot (le_of_lt h₂lt) hhi₂
  · rcases le_iff_eq_or_lt.mp hmid₂ with h₂eq | h₂lt
    · linarith [h₁lt, h₂eq]
    · exact b4UltimateEnvelope_mono_on_hi h₁lt h₂lt hhi₁ hhi₂ h

private lemma b4UltimateEnvelope_mono_to_lo_knot {wc : ℚ} (h : wc ≤ b4WcLo) :
    b4UltimateEnvelope wc ≤ b4UltimateEnvelope b4WcLo :=
  b4UltimateEnvelope_mono_on_lo h (le_refl b4WcLo) h

private lemma b4UltimateEnvelope_mono_cross_lo_critical {wc₁ wc₂ : ℚ}
    (hlo₁ : wc₁ ≤ b4WcLo) (hlo₂ : b4WcLo < wc₂) (hcrit₂ : wc₂ ≤ criticalWcChemPin) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ :=
  le_trans (b4UltimateEnvelope_mono_to_lo_knot hlo₁)
    (b4UltimateEnvelope_mono_from_lo_knot (le_of_lt hlo₂) hcrit₂)

private lemma b4UltimateEnvelope_mono_cross_lo_mid {wc₁ wc₂ : ℚ}
    (hlo₁ : wc₁ ≤ b4WcLo) (hcrit₂ : criticalWcChemPin < wc₂) (hmid₂ : wc₂ ≤ b4WcMid) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ :=
  le_trans (b4UltimateEnvelope_mono_to_lo_knot hlo₁)
    (le_trans b4UltimateEnvelope_knots_mono_lo_critical
      (b4UltimateEnvelope_mono_from_critical_knot (le_of_lt hcrit₂) hmid₂))

private lemma b4UltimateEnvelope_mono_cross_lo_hi {wc₁ wc₂ : ℚ}
    (hlo₁ : wc₁ ≤ b4WcLo) (hmid₂ : b4WcMid < wc₂) (hhi₂ : wc₂ ≤ b4WcHi) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ :=
  le_trans (b4UltimateEnvelope_mono_to_lo_knot hlo₁)
    (le_trans b4UltimateEnvelope_knots_mono_lo_critical
      (le_trans b4UltimateEnvelope_knots_mono_critical_mid
        (b4UltimateEnvelope_mono_from_mid_knot (le_of_lt hmid₂) hhi₂)))

private lemma b4UltimateEnvelope_mono_cross_critical_mid {wc₁ wc₂ : ℚ}
    (hlo₁ : b4WcLo < wc₁) (hcrit₁ : wc₁ ≤ criticalWcChemPin) (hcrit₂ : criticalWcChemPin < wc₂)
    (hmid₂ : wc₂ ≤ b4WcMid) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ :=
  le_trans (b4UltimateEnvelope_mono_on_critical_closed (le_of_lt hlo₁) hcrit₁
      b4WcLo_le_critical (le_refl criticalWcChemPin) hcrit₁)
    (b4UltimateEnvelope_mono_from_critical_knot (le_of_lt hcrit₂) hmid₂)

private lemma b4UltimateEnvelope_mono_cross_critical_hi {wc₁ wc₂ : ℚ}
    (hlo₁ : b4WcLo < wc₁) (hcrit₁ : wc₁ ≤ criticalWcChemPin) (hmid₂ : b4WcMid < wc₂)
    (hhi₂ : wc₂ ≤ b4WcHi) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ :=
  le_trans (b4UltimateEnvelope_mono_on_critical_closed (le_of_lt hlo₁) hcrit₁
      b4WcLo_le_critical (le_refl criticalWcChemPin) hcrit₁)
    (le_trans b4UltimateEnvelope_knots_mono_critical_mid
      (b4UltimateEnvelope_mono_from_mid_knot (le_of_lt hmid₂) hhi₂))

private lemma b4UltimateEnvelope_mono_cross_mid_hi {wc₁ wc₂ : ℚ}
    (hcrit₁ : criticalWcChemPin < wc₁) (hmid₁ : wc₁ ≤ b4WcMid) (hmid₂ : b4WcMid < wc₂)
    (hhi₂ : wc₂ ≤ b4WcHi) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ :=
  le_trans (b4UltimateEnvelope_mono_on_mid_closed (le_of_lt hcrit₁) hmid₁
      critical_le_b4WcMid (le_refl b4WcMid) hmid₁)
    (b4UltimateEnvelope_mono_from_mid_knot (le_of_lt hmid₂) hhi₂)

theorem envelope_global_mono_cross_knot {wc₁ wc₂ : ℚ}
    (hwc₁ : b4WcAdmissible wc₁) (hwc₂ : b4WcAdmissible wc₂) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ := by
  rcases hwc₁ with ⟨_, hhi₁⟩
  rcases hwc₂ with ⟨_, hhi₂⟩
  by_cases hlo₁ : wc₁ ≤ b4WcLo
  · by_cases hlo₂ : wc₂ ≤ b4WcLo
    · exact b4UltimateEnvelope_mono_on_lo hlo₁ hlo₂ h
    · by_cases hcrit₂ : wc₂ ≤ criticalWcChemPin
      · exact b4UltimateEnvelope_mono_cross_lo_critical hlo₁ (lt_of_not_ge hlo₂) hcrit₂ h
      · by_cases hmid₂ : wc₂ ≤ b4WcMid
        · exact b4UltimateEnvelope_mono_cross_lo_mid hlo₁ (lt_of_not_ge hcrit₂) hmid₂ h
        · exact b4UltimateEnvelope_mono_cross_lo_hi hlo₁ (lt_of_not_ge hmid₂) hhi₂ h
  · by_cases hcrit₁ : wc₁ ≤ criticalWcChemPin
    · by_cases hlo₂ : wc₂ ≤ b4WcLo
      · linarith [hlo₂, h]
      · by_cases hcrit₂ : wc₂ ≤ criticalWcChemPin
        · exact b4UltimateEnvelope_mono_on_critical (lt_of_not_ge hlo₁) (lt_of_not_ge hlo₂) hcrit₁ hcrit₂ h
        · by_cases hmid₂ : wc₂ ≤ b4WcMid
          · exact b4UltimateEnvelope_mono_cross_critical_mid (lt_of_not_ge hlo₁) hcrit₁
              (lt_of_not_ge hcrit₂) hmid₂ h
          · exact b4UltimateEnvelope_mono_cross_critical_hi (lt_of_not_ge hlo₁) hcrit₁
              (lt_of_not_ge hmid₂) hhi₂ h
    · by_cases hlo₂ : wc₂ ≤ b4WcLo
      · linarith [hlo₂, h]
      · by_cases hcrit₂ : wc₂ ≤ criticalWcChemPin
        · linarith [hcrit₂, hcrit₁]
        · by_cases hmid₂ : wc₂ ≤ b4WcMid
          · have hmid₁ : wc₁ ≤ b4WcMid := le_trans h hmid₂
            exact b4UltimateEnvelope_mono_on_mid (lt_of_not_ge hcrit₁) (lt_of_not_ge hcrit₂) hmid₁ hmid₂ h
          · by_cases hmid₁ : wc₁ ≤ b4WcMid
            · exact b4UltimateEnvelope_mono_cross_mid_hi (lt_of_not_ge hcrit₁) hmid₁
                (lt_of_not_ge hmid₂) hhi₂ h
            · exact b4UltimateEnvelope_mono_on_hi (lt_of_not_ge hmid₁) (lt_of_not_ge hmid₂) hhi₁ hhi₂ h

theorem b4UltimateEnvelope_mono {wc₁ wc₂ : ℚ}
    (hwc₁ : b4WcAdmissible wc₁) (hwc₂ : b4WcAdmissible wc₂) (h : wc₁ ≤ wc₂) :
    b4UltimateEnvelope wc₁ ≤ b4UltimateEnvelope wc₂ :=
  envelope_global_mono_cross_knot hwc₁ hwc₂ h

noncomputable def alphaUlt (wc : ℚ) : ℚ := min (wc / criticalWcChemPin) 1

noncomputable def shrinkageDevelopment (α α_ult : ℚ) : ℚ :=
  if α_ult ≤ 0 then α else min (α / α_ult) 1

lemma shrinkageDevelopment_nonneg {α α_ult : ℚ} (hα : 0 ≤ α) :
    0 ≤ shrinkageDevelopment α α_ult := by
  unfold shrinkageDevelopment; split_ifs with h <;> [exact hα; exact le_min (div_nonneg hα (le_of_lt (not_le.mp h))) (by norm_num)]

lemma shrinkageDevelopment_le_one {α α_ult : ℚ} (hα : α ≤ 1) :
    shrinkageDevelopment α α_ult ≤ 1 := by
  unfold shrinkageDevelopment; split_ifs <;> [linarith; exact min_le_right _ _]

lemma alphaUlt_mono {wc₁ wc₂ : ℚ} (h : wc₁ ≤ wc₂) : alphaUlt wc₁ ≤ alphaUlt wc₂ := by
  unfold alphaUlt; refine min_le_min ?_ (le_refl _); exact div_le_div_of_nonneg_right h (le_of_lt criticalWcChemPin_pos)

lemma shrinkageDevelopment_mono_in_degree {α₁ α₂ α_ult : ℚ}
    (hα : α₁ ≤ α₂) (hult : 0 < α_ult) :
    shrinkageDevelopment α₁ α_ult ≤ shrinkageDevelopment α₂ α_ult := by
  unfold shrinkageDevelopment; simp only [not_le.mpr hult, ↓reduceIte]
  refine min_le_min ?_ (le_refl _); exact div_le_div_of_nonneg_right hα (le_of_lt hult)

lemma shrinkageDevelopment_mono_in_degree_admissible {α₁ α₂ α_ult : ℚ}
    (hα : α₁ ≤ α₂) :
    shrinkageDevelopment α₁ α_ult ≤ shrinkageDevelopment α₂ α_ult := by
  unfold shrinkageDevelopment
  by_cases hult : α_ult ≤ 0
  · simp [hult, hα]
  · simp only [hult, ↓reduceIte]
    refine min_le_min ?_ (le_refl _)
    exact div_le_div_of_nonneg_right hα (le_of_lt (lt_of_not_ge hult))

open Real

noncomputable def shrinkageDevelopmentExp (α α_ult : ℝ) : ℝ :=
  if α_ult ≤ 0 then α else max 0 (min 1 (1 - exp (-3 * α / α_ult)))

private lemma one_sub_exp_neg_three_div_mono {α₁ α₂ α_ult : ℝ}
    (hα : α₁ ≤ α₂) (hult : 0 < α_ult) :
    (1 - exp (-3 * α₁ / α_ult)) ≤ (1 - exp (-3 * α₂ / α_ult)) := by
  have hmul : -3 * α₂ ≤ -3 * α₁ := by linarith
  have hneg : -3 * α₂ / α_ult ≤ -3 * α₁ / α_ult :=
    div_le_div_of_nonneg_right hmul (le_of_lt hult)
  have hexp : exp (-3 * α₂ / α_ult) ≤ exp (-3 * α₁ / α_ult) := exp_monotone hneg
  linarith

lemma shrinkageDevelopmentExp_nonneg {α α_ult : ℝ} (hα : 0 ≤ α) :
    0 ≤ shrinkageDevelopmentExp α α_ult := by
  unfold shrinkageDevelopmentExp; split_ifs <;> [exact hα; exact le_max_left 0 _]

lemma shrinkageDevelopmentExp_le_one {α α_ult : ℝ} (hα : α ≤ 1) :
    shrinkageDevelopmentExp α α_ult ≤ 1 := by
  unfold shrinkageDevelopmentExp
  split_ifs with h
  · linarith
  · refine max_le_iff.mpr ⟨?_, min_le_left _ _⟩
    exact zero_le_one

theorem shrinkageDevelopmentExp_at_zero (α_ult : ℝ) :
    shrinkageDevelopmentExp 0 α_ult =
      if α_ult ≤ 0 then 0 else max 0 (min 1 0) := by
  unfold shrinkageDevelopmentExp; split_ifs <;> simp [exp_zero]

lemma shrinkageDevelopmentExp_mono_in_degree {α₁ α₂ α_ult : ℝ}
    (hα : α₁ ≤ α₂) (hult : 0 < α_ult) :
    shrinkageDevelopmentExp α₁ α_ult ≤ shrinkageDevelopmentExp α₂ α_ult := by
  unfold shrinkageDevelopmentExp
  simp only [not_le.mpr hult, ↓reduceIte]
  exact max_le_max le_rfl (min_le_min le_rfl (one_sub_exp_neg_three_div_mono hα hult))

lemma shrinkageDevelopment_coe_rational {α α_ult : ℚ} (hult : 0 < α_ult) :
    (shrinkageDevelopment α α_ult : ℝ) = min ((α : ℝ) / (α_ult : ℝ)) 1 := by
  unfold shrinkageDevelopment
  simp only [not_le.mpr hult, ↓reduceIte, Rat.cast_min, Rat.cast_div, Rat.cast_one]

theorem shrinkageDevelopment_parallel_bounds {α α_ult : ℚ}
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (_hult : 0 < α_ult) :
    0 ≤ shrinkageDevelopment α α_ult ∧
      shrinkageDevelopment α α_ult ≤ 1 ∧
        0 ≤ shrinkageDevelopmentExp (α : ℝ) (α_ult : ℝ) ∧
          shrinkageDevelopmentExp (α : ℝ) (α_ult : ℝ) ≤ 1 :=
  ⟨shrinkageDevelopment_nonneg hα₀, shrinkageDevelopment_le_one hα₁,
    shrinkageDevelopmentExp_nonneg (by exact_mod_cast hα₀),
    shrinkageDevelopmentExp_le_one (by exact_mod_cast hα₁)⟩

noncomputable def pasteFactor (cement_kg : ℚ) : ℚ :=
  if 0 ≤ cement_kg then cement_kg / 350 else 0

noncomputable def scmFactor (scm_ratio : ℚ) : ℚ := 1 + scm_ratio * (3 / 10)

structure AutogenousShrinkageInput where
  wc_ratio : ℚ
  degree_hydration : ℚ
  cement_content_kg : ℚ
  scm_ratio : ℚ

def shrinkageInputAdmissible (input : AutogenousShrinkageInput) : Prop :=
  b4WcAdmissible input.wc_ratio ∧
    0 ≤ input.degree_hydration ∧ input.degree_hydration ≤ 1 ∧
    0 < input.cement_content_kg ∧ -(10 / 3) ≤ input.scm_ratio

noncomputable def autogenousShrinkageMicrostrain (input : AutogenousShrinkageInput) : ℚ :=
  let α_ult := alphaUlt input.wc_ratio
  let development := shrinkageDevelopment input.degree_hydration α_ult
  b4UltimateEnvelope input.wc_ratio * development *
    pasteFactor input.cement_content_kg * scmFactor input.scm_ratio

theorem autogenousShrinkageMicrostrain_nonpos {input : AutogenousShrinkageInput}
    (h : shrinkageInputAdmissible input) :
    autogenousShrinkageMicrostrain input ≤ 0 := by
  dsimp [autogenousShrinkageMicrostrain]
  rcases h with ⟨hwc, hα0, _, _, _⟩
  have henvelope := b4UltimateEnvelope_nonpos hwc
  have hdev := shrinkageDevelopment_nonneg (α := input.degree_hydration) (α_ult := alphaUlt input.wc_ratio) hα0
  have hpaste : 0 ≤ pasteFactor input.cement_content_kg := by unfold pasteFactor; split_ifs <;> linarith
  have hscm : 0 ≤ scmFactor input.scm_ratio := by unfold scmFactor; nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg henvelope hdev) hpaste) hscm

inductive B2OpenObligation
  | transcendental_development_bridge
  | paste_factor_sqrt_bridge
  | full_compose_stack_cd_closure
  | operator_epsilon_calibration
  deriving DecidableEq, Repr

def b2OpenObligationCertId : String := "CC-P-B2-1"

def b2OpenObligationDescription : B2OpenObligation → String
  | .transcendental_development_bridge =>
      "prove rational scaffold approximates ℝ exp(-3α/α_ult) within operator ε on admissible box"
  | .paste_factor_sqrt_bridge =>
      "prove sqrt(cement/350) paste factor matches rational scaffold or tighten domain"
  | .full_compose_stack_cd_closure =>
      "end-to-end Clausius–Duhem closure for B2 compose stack (beyond slice-1 scalar)"
  | .operator_epsilon_calibration =>
      "measured ε bounds + operator B2-O1 anchor — P3/P4/P5 cert gate"

#print axioms shrinkageDevelopmentExp_mono_in_degree
#print axioms shrinkageDevelopment_parallel_bounds
#print axioms shrinkageDevelopment_mono_in_degree
#print axioms alphaUlt_mono

end UMST

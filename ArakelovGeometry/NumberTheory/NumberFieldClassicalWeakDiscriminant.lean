/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberFieldClassicalComparisonConstantMonotone
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-! # The discriminant correction in the classical h0 comparison -/

@[expose] public section

noncomputable section
open NumberField

namespace ArakelovGeometry.NumberFieldClassicalWeakDiscriminant

variable (K : Type*) [Field K] [NumberField K]

/-- The actual field discriminant absorbs one factor two at each complex place. -/
theorem two_pow_nrComplex_le_abs_discr :
    (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K ≤ |(NumberField.discr K : ℝ)| := by
  let d := Module.finrank ℚ K
  let r := InfinitePlace.nrComplexPlaces K
  have hdr : 2 * r ≤ d := by
    have h := InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  by_cases hr : r = 0
  · change (2 : ℝ) ^ r ≤ _
    rw [hr, pow_zero]
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)
  have hd : 2 ≤ d := by omega
  have hM := NumberField.abs_discr_ge (K := K) (by omega : 1 < Module.finrank ℚ K)
  push_cast at hM
  have hπ : (9 / 4 : ℝ) ≤ 3 * Real.pi / 4 := by nlinarith [Real.pi_gt_three]
  have hP := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 4) hπ d
  have hq : (9 / 4 : ℝ) ≤ (3 / 2 : ℝ) ^ d := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2) hd
    norm_num at h ⊢
    exact h
  have hsq : ((3 / 2 : ℝ) ^ d) ^ 2 = (9 / 4 : ℝ) ^ d := by
    rw [← pow_mul, Nat.mul_comm d 2, pow_mul]
    norm_num
  have hmain : (3 / 2 : ℝ) ^ d ≤ |(NumberField.discr K : ℝ)| := by
    have h := (mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 4 / 9)).trans hM
    rw [← hsq] at h
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) d)]
  calc
    (2 : ℝ) ^ r ≤ (9 / 4 : ℝ) ^ r :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (3 / 2 : ℝ) ^ (2 * r) := by rw [pow_mul]; norm_num
    _ ≤ (3 / 2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hdr
    _ ≤ _ := hmain

/-- The signed trace-degree correction is bounded by the actual log discriminant. -/
theorem traceDegree_correction_le_log_discr :
    max 0 (-(Real.log |(NumberField.discr K : ℝ)| -
      2 * (InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2)) ≤
        Real.log |(NumberField.discr K : ℝ)| := by
  have h := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K)
    (two_pow_nrComplex_le_abs_discr K)
  rw [Real.log_pow] at h
  exact max_le (NumberFieldPureMinkowskiLevels.log_abs_discriminant_nonneg (K := K))
    (by linarith)

end ArakelovGeometry.NumberFieldClassicalWeakDiscriminant

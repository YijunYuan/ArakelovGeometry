/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import ArakelovGeometry.NumberTheory.NumberField.Covolume.Integer
import Mathlib.Topology.Sheaves.Init

/-! # The actual scalar normalization and radius in the arithmetic Minkowski estimate -/

@[expose] public section

noncomputable section
open NumberField

namespace ArakelovGeometry.NumberFieldMinkowskiRadius

variable (K : Type*) [Field K] [NumberField K]

/-- The logarithm of the actual ordinary covolume of the integer ring. -/
theorem log_covolume_constant :
    Real.log ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
      Real.sqrt |(NumberField.discr K : ℝ)|) =
      -(InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 +
        Real.log |(NumberField.discr K : ℝ)| / 2 := by
  have hd := NumberFieldActualIntegerCovolume.discriminant_abs_pos K
  have hs := Real.sqrt_pos.mpr hd
  have hp : 0 < (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K := by positivity
  rw [Real.log_mul hp.ne' hs.ne', Real.log_pow, Real.log_inv, Real.log_sqrt hd.le]
  ring

/-- The product-ball radius used for an actual bundle of rank `n` and degree `D`. -/
def radius (n : ℕ) (D : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.exp ((-(D / (n : ℝ)) +
    Real.log |(NumberField.discr K : ℝ)| / 2) / (Module.finrank ℚ K : ℝ))

theorem radius_pos {n : ℕ} (hn : 0 < n) (D : ℝ) : 0 < radius K n D :=
  mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hn)) (Real.exp_pos _)

theorem radius_div_sqrt {n : ℕ} (hn : 0 < n) (D : ℝ) :
    radius K n D / Real.sqrt (n : ℝ) =
      Real.exp ((-(D / (n : ℝ)) + Real.log |(NumberField.discr K : ℝ)| / 2) /
        (Module.finrank ℚ K : ℝ)) :=
  mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'

theorem radius_quotient_pow {n : ℕ} (hn : 0 < n) (D : ℝ) :
    (radius K n D / Real.sqrt (n : ℝ)) ^ (Module.finrank ℚ K * n) =
      Real.exp (-D + (n : ℝ) * Real.log |(NumberField.discr K : ℝ)| / 2) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  rw [radius_div_sqrt K hn D, ← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The actual cube volume equals the exact Minkowski threshold. -/
theorem volume_threshold_identity {n : ℕ} (hn : 0 < n) (D : ℝ) :
    (2 : ℝ) ^ (n * Fintype.card (InfinitePlace K)) *
        (radius K n D / Real.sqrt (n : ℝ)) ^ (Module.finrank ℚ K * n) =
      Real.exp (-D + (n : ℝ) * Real.log
        ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K : ℝ)|)) *
        (2 : ℝ) ^ (Module.finrank ℚ K * n) := by
  have hc : Fintype.card (InfinitePlace K) + InfinitePlace.nrComplexPlaces K =
      Module.finrank ℚ K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    have := InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  rw [radius_quotient_pow K hn D,
    ← Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2)
      (n * Fintype.card (InfinitePlace K))),
    ← Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2)
      (Module.finrank ℚ K * n)), ← Real.exp_add, ← Real.exp_add,
    Real.log_pow, Real.log_pow, log_covolume_constant]
  congr 1
  rw [← hc]
  push_cast
  ring

theorem neg_rank_mul_log_radius {n : ℕ} (hn : 0 < n) (D : ℝ) :
    -(Module.finrank ℚ K : ℝ) * Real.log (radius K n D) =
      D / (n : ℝ) - (Module.finrank ℚ K : ℝ) / 2 * Real.log (n : ℝ) -
        Real.log |(NumberField.discr K : ℝ)| / 2 := by
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sqrt_pos.mpr hn'
  rw [radius, Real.log_mul hs.ne' (Real.exp_pos _).ne', Real.log_sqrt hn'.le,
    Real.log_exp]
  field_simp
  ring

end ArakelovGeometry.NumberFieldMinkowskiRadius

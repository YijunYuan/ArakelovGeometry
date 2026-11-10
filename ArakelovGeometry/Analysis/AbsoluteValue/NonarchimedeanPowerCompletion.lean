/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module


public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive powers of genuine non-Archimedean completions

Positive powers change the absolute value while preserving the completed
topological field. This supplies the local normalization bridge needed for
the source-normalized number-field data.
-/

@[expose] public section

noncomputable section
open Topology

namespace AbsoluteValue

variable {K : Type*} [Field K]

/-- A positive power of a genuine non-Archimedean absolute value. -/
def nonarchimedeanRpow (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (θ : ℝ) (hθ : 0 < θ) : AbsoluteValue K ℝ where
  toFun x := v x ^ θ
  map_mul' x y := by rw [map_mul, Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) θ
  eq_zero' x := (Real.rpow_eq_zero (v.nonneg x) hθ.ne').trans v.eq_zero
  add_le' x y := by
    calc
      v (x + y) ^ θ ≤ max (v x) (v y) ^ θ :=
        Real.rpow_le_rpow (v.nonneg _) (hv x y) hθ.le
      _ = max (v x ^ θ) (v y ^ θ) := Real.rpow_max (v.nonneg x) (v.nonneg y) hθ.le
      _ ≤ v x ^ θ + v y ^ θ := max_le_iff.mpr
        ⟨le_add_of_nonneg_right (Real.rpow_nonneg (v.nonneg y) θ),
         le_add_of_nonneg_left (Real.rpow_nonneg (v.nonneg x) θ)⟩

@[simp]
theorem nonarchimedeanRpow_apply (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (θ : ℝ) (hθ : 0 < θ) (x : K) : nonarchimedeanRpow v hv θ hθ x = v x ^ θ := rfl

/-- The powered absolute value retains the actual ultrametric inequality. -/
theorem isNonarchimedean_nonarchimedeanRpow (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (θ : ℝ) (hθ : 0 < θ) :
    IsNonarchimedean (nonarchimedeanRpow v hv θ hθ) := by
  intro x y
  change v (x + y) ^ θ ≤ max (v x ^ θ) (v y ^ θ)
  rw [← Real.rpow_max (v.nonneg x) (v.nonneg y) hθ.le]
  exact Real.rpow_le_rpow (v.nonneg _) (hv x y) hθ.le

/-- Positive powers give equivalent absolute values, including the trivial one. -/
theorem isEquiv_nonarchimedeanRpow (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (θ : ℝ) (hθ : 0 < θ) :
    v.IsEquiv (nonarchimedeanRpow v hv θ hθ) := by
  intro x y
  exact (Real.rpow_le_rpow_iff (v.nonneg x) (v.nonneg y) hθ).symm

/-- The identity of the original field gives the canonical ring equivalence
between its actual completions before and after taking a positive power. -/
def nonarchimedeanRpowCompletionEquiv (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (θ : ℝ) (hθ : 0 < θ) :
    v.Completion ≃+* (nonarchimedeanRpow v hv θ hθ).Completion :=
  UniformSpace.Completion.mapRingEquiv (WithAbs.congr v _ (.refl K))
    ((isEquiv_iff_isHomeomorph v _).mp (isEquiv_nonarchimedeanRpow v hv θ hθ)).continuous
    (by
      rw [WithAbs.congr_symm]
      exact ((isEquiv_iff_isHomeomorph _ v).mp
        (isEquiv_nonarchimedeanRpow v hv θ hθ).symm).continuous)

@[simp]
theorem nonarchimedeanRpowCompletionEquiv_coe (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (θ : ℝ) (hθ : 0 < θ) (x : K) :
    nonarchimedeanRpowCompletionEquiv v hv θ hθ (x : v.Completion) =
      (x : (nonarchimedeanRpow v hv θ hθ).Completion) := by
  exact UniformSpace.Completion.mapRingHom_coe
    ((isEquiv_iff_isHomeomorph v _).mp (isEquiv_nonarchimedeanRpow v hv θ hθ)).continuous
    (WithAbs.toAbs v x)

/-- The genuine completed power isomorphism is continuous. -/
theorem continuous_nonarchimedeanRpowCompletionEquiv (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (θ : ℝ) (hθ : 0 < θ) :
    Continuous (nonarchimedeanRpowCompletionEquiv v hv θ hθ) :=
  UniformSpace.Completion.continuous_map

/-- Its genuine completed inverse is continuous too. -/
theorem continuous_nonarchimedeanRpowCompletionEquiv_symm (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (θ : ℝ) (hθ : 0 < θ) :
    Continuous (nonarchimedeanRpowCompletionEquiv v hv θ hθ).symm :=
  UniformSpace.Completion.continuous_map

/-- The canonical actual completion map has the powered norm on every vector. -/
theorem norm_nonarchimedeanRpowCompletionEquiv (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (θ : ℝ) (hθ : 0 < θ) (z : v.Completion) :
    ‖nonarchimedeanRpowCompletionEquiv v hv θ hθ z‖ = ‖z‖ ^ θ := by
  let e := nonarchimedeanRpowCompletionEquiv v hv θ hθ
  have he : Continuous e := continuous_nonarchimedeanRpowCompletionEquiv v hv θ hθ
  change ‖e z‖ = ‖z‖ ^ θ
  refine UniformSpace.Completion.induction_on
    (p := fun z : v.Completion => ‖e z‖ = ‖z‖ ^ θ) z ?_ ?_
  · exact isClosed_eq (continuous_norm.comp he)
      (continuous_norm.rpow_const (fun _ => Or.inr hθ.le))
  · intro a
    rw [UniformSpace.Completion.norm_coe]
    change ‖nonarchimedeanRpowCompletionEquiv v hv θ hθ
      ((WithAbs.ofAbs a : K) : v.Completion)‖ = ‖a‖ ^ θ
    rw [nonarchimedeanRpowCompletionEquiv_coe, UniformSpace.Completion.norm_coe]
    rfl

/-- The actual completed valuation-ring unit ball is unchanged under the
canonical positive-power field isomorphism. -/
theorem norm_nonarchimedeanRpowCompletionEquiv_le_one_iff (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (θ : ℝ) (hθ : 0 < θ) (z : v.Completion) :
    ‖nonarchimedeanRpowCompletionEquiv v hv θ hθ z‖ ≤ 1 ↔ ‖z‖ ≤ 1 := by
  rw [norm_nonarchimedeanRpowCompletionEquiv]
  simpa only [Real.one_rpow] using
    (Real.rpow_le_rpow_iff (norm_nonneg z) zero_le_one hθ)

/-- Logarithms of the actual powered absolute value have the expected factor,
also at zero with the real logarithm convention. -/
theorem log_nonarchimedeanRpow (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (θ : ℝ) (hθ : 0 < θ) (x : K) :
    Real.log (nonarchimedeanRpow v hv θ hθ x) = θ * Real.log (v x) := by
  by_cases hx : x = 0
  · subst x
    simp
  · exact Real.log_rpow (v.pos hx) θ

/-- Inverse-power weights preserve the logarithm of every genuine completed
vector under the canonical field isomorphism. -/
theorem inv_mul_log_norm_nonarchimedeanRpowCompletionEquiv (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (θ : ℝ) (hθ : 0 < θ) (z : v.Completion) :
    θ⁻¹ * Real.log ‖nonarchimedeanRpowCompletionEquiv v hv θ hθ z‖ =
      Real.log ‖z‖ := by
  rw [norm_nonarchimedeanRpowCompletionEquiv]
  by_cases hz : z = 0
  · subst z
    simp [Real.zero_rpow hθ.ne']
  · rw [Real.log_rpow (norm_pos_iff.mpr hz), ← mul_assoc, inv_mul_cancel₀ hθ.ne', one_mul]

end AbsoluteValue

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Height.Basic

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Affine heights and the Northcott property

The height of `(1, a)` is nonnegative and homogeneous under powers.
For a proper adelic structure it bounds the heights of all normalized coordinates.
The Northcott property of Definition 3.5.2 is finiteness of its bounded sublevel sets.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure

open MeasureTheory

variable {K : Type*} [Field K] (AS : AdelicStructure K)

theorem localHeight_pair (a b : K) (ω : AS.Ω) :
    AS.localHeight ![a, b] ω = max (AS.ϕ ω a) (AS.ϕ ω b) := by
  simp [localHeight, Finset.univ_fin2, Finset.sup'_insert, Finset.sup'_singleton]

/-- The affine logarithmic height is the logarithmic height of the tuple `(1, a)`. -/
noncomputable def affineLogHeight (a : K) : ℝ := AS.logHeight ![1, a]

theorem affineLogHeight_eq_integral (a : K) :
    AS.affineLogHeight a = ∫ ω, Real.log (max 1 (AS.ϕ ω a)) ∂AS.v := by
  simp [affineLogHeight, logHeight, localHeight_pair]

theorem integrable_log_max_one (a : K) :
    Integrable (fun ω ↦ Real.log (max 1 (AS.ϕ ω a))) AS.v := by
  simpa only [localHeight_pair, map_one] using AS.integrable_log_localHeight ![1, a]

theorem affineLogHeight_nonneg (a : K) : 0 ≤ AS.affineLogHeight a := by
  rw [AS.affineLogHeight_eq_integral]
  exact integral_nonneg (fun ω ↦ Real.log_nonneg (le_max_left _ _))

@[simp] theorem affineLogHeight_zero : AS.affineLogHeight 0 = 0 := by
  simp [affineLogHeight_eq_integral]

@[simp] theorem affineLogHeight_one : AS.affineLogHeight 1 = 0 := by
  simp [affineLogHeight_eq_integral]

@[simp] theorem affineLogHeight_neg (a : K) : AS.affineLogHeight (-a) = AS.affineLogHeight a := by
  simp [affineLogHeight_eq_integral]

/-- Raising an element to the `m`th power multiplies its affine height by `m`. -/
theorem affineLogHeight_pow (a : K) (m : ℕ) :
    AS.affineLogHeight (a ^ m) = m * AS.affineLogHeight a := by
  have hmax (ω : AS.Ω) : max (1 : ℝ) (AS.ϕ ω (a ^ m)) =
      (max 1 (AS.ϕ ω a)) ^ m := by
    rw [map_pow]
    rcases le_total (AS.ϕ ω a) 1 with h | h
    · rw [max_eq_left h, max_eq_left (pow_le_one₀ ((AS.ϕ ω).nonneg a) h), one_pow]
    · rw [max_eq_right h, max_eq_right (one_le_pow₀ h)]
  simp only [AS.affineLogHeight_eq_integral, hmax, Real.log_pow, integral_const_mul]

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A coordinate in an affine chart has height bounded by the tuple height. -/
theorem affineLogHeight_le_logHeight_of_eq_one (a : ι → K) {j : ι} (hj : a j = 1)
    (i : ι) : AS.affineLogHeight (a i) ≤ AS.logHeight a := by
  rw [AS.affineLogHeight_eq_integral]
  apply integral_mono (AS.integrable_log_max_one _) (AS.integrable_log_localHeight a)
  intro ω
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  apply max_le
  · simpa only [hj, map_one] using AS.eval_le_localHeight a ω j
  · exact AS.eval_le_localHeight a ω i

/-- The Northcott property means finite affine height sublevel sets over the base field. -/
class HasNorthcott : Prop where
  /-- The defining property. -/
  finite_sublevel :
    ∀ C : ℝ, 0 ≤ C → Set.Finite {a : K | AS.affineLogHeight a ≤ C}

instance : CoeFun (AS.HasNorthcott)
    (fun _ ↦
      ∀ C : ℝ, 0 ≤ C → Set.Finite {a : K | AS.affineLogHeight a ≤ C}) :=
  ⟨fun h ↦ h.finite_sublevel⟩

/-- The defining proposition of `HasNorthcott`. -/
theorem HasNorthcott.iff :
    AS.HasNorthcott ↔
    ∀ C : ℝ, 0 ≤ C → Set.Finite {a : K | AS.affineLogHeight a ≤ C} :=
  ⟨fun h ↦ h.finite_sublevel, fun h ↦ ⟨h⟩⟩

/-- Negative bounds give the empty set, so the nonnegative restriction is immaterial. -/
theorem hasNorthcott_iff : AS.HasNorthcott ↔
    ∀ C : ℝ, Set.Finite {a : K | AS.affineLogHeight a ≤ C} := by
  constructor
  · intro h C
    by_cases hC : 0 ≤ C
    · exact h C hC
    · have he : {a : K | AS.affineLogHeight a ≤ C} = ∅ := by
        ext a
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact not_le.mpr ((lt_of_not_ge hC).trans_le (AS.affineLogHeight_nonneg a))
      rw [he]
      exact Set.finite_empty
  · exact fun h ↦ ⟨fun C _ ↦ h C⟩

variable [AS.IsProper]

theorem affineLogHeight_eq_projectiveLogHeight (a : K) :
    AS.affineLogHeight a = AS.projectiveLogHeight
      (Projectivization.mk K ![1, a] (by
        intro h
        have := congrFun h 0
        simp at this)) := rfl

/-- Every normalized coordinate of a projective point is bounded by its height. -/
theorem affineLogHeight_div_le_logHeight (a : ι → K) {j : ι} (hj : a j ≠ 0) (i : ι) :
    AS.affineLogHeight (a i / a j) ≤ AS.logHeight a := by
  have ha : a ≠ 0 := by
    intro h
    exact hj (congrFun h j)
  have h := AS.affineLogHeight_le_logHeight_of_eq_one ((a j)⁻¹ • a)
    (j := j) (by simp [hj]) i
  simpa only [AS.logHeight_smul_eq ha (inv_ne_zero hj), Pi.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using h

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.AdelicCurve

/-- The Northcott property of an adelic curve is that of its adelic structure. -/
abbrev HasNorthcott (C : AdelicCurve) : Prop := C.AS.HasNorthcott

end ArakelovGeometry.AdelicCurve

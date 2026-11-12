/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Domination.Counting

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import Mathlib.CategoryTheory.Category.Init

/-!
# Generic cheap-line norms on the rational counting curve

The cost remains an arbitrary real number in `(0, 1]`. The canonical
completed tensor equivalence is the accepted trivial-completion map.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.MinkowskiCounting

noncomputable section

open AdelicStructure CountingDominationCounterexample

local instance : DecidablePred (fun x : ℚ ↦ x = 0) :=
  fun _ ↦ Classical.propDecidable _

/-- The generic source cheap-line norm before completed-fibre transport. -/
def rawNorm (c : ℝ) (a : ℚ) (x : Plane) : ℝ :=
  if x = 0 then 0 else if x.2 = a * x.1 then c else 1

@[simp]
theorem rawNorm_zero (c : ℝ) (a : ℚ) : rawNorm c a 0 = 0 := by
  simp [rawNorm]

/-- All values are bounded by one, including the zero vector. -/
theorem rawNorm_le_one {c : ℝ} (hc : c ≤ 1) (a : ℚ) (x : Plane) :
    rawNorm c a x ≤ 1 := by
  simp only [rawNorm]
  split_ifs
  · norm_num
  · exact hc
  · exact le_rfl

/-- Every nonzero vector has the positive generic lower bound. -/
theorem cost_le_rawNorm {c : ℝ} (hc : c ≤ 1) (a : ℚ) {x : Plane} (hx : x ≠ 0) :
    c ≤ rawNorm c a x := by
  simp only [rawNorm, ite_eq_right hx]
  split_ifs
  · exact le_rfl
  · exact hc

/-- Positivity of the cost produces separation. -/
theorem rawNorm_eq_zero_iff {c : ℝ} (hc : 0 < c) (a : ℚ) (x : Plane) :
    rawNorm c a x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [rawNorm, ite_eq_right hx]
    split_ifs <;> simp [hc.ne', hx]

/-- The generic cost works because the cheap locus is an actual subspace. -/
theorem rawNorm_add_le_max {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (a : ℚ) (x y : Plane) :
    rawNorm c a (x + y) ≤ max (rawNorm c a x) (rawNorm c a y) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  by_cases hxl : x.2 = a * x.1
  · by_cases hyl : y.2 = a * y.1
    · have hsum : (x + y).2 = a * (x + y).1 := by
        simp only [Prod.fst_add, Prod.snd_add, hxl, hyl, mul_add]
      simp only [rawNorm, ite_eq_right hx, ite_eq_right hy, ite_eq_left hxl, ite_eq_left hyl,
        max_self]
      by_cases hxy : x + y = 0
      · simpa [hxy] using hc
      · simp [hxy, hsum]
    · have hright : rawNorm c a y = 1 := by simp [rawNorm, hy, hyl]
      rw [hright]
      exact (rawNorm_le_one hc1 a (x + y)).trans (le_max_right _ _)
  · have hleft : rawNorm c a x = 1 := by simp [rawNorm, hx, hxl]
    rw [hleft]
    exact (rawNorm_le_one hc1 a (x + y)).trans (le_max_left _ _)

theorem rawNorm_add_le {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (a : ℚ) (x y : Plane) : rawNorm c a (x + y) ≤ rawNorm c a x + rawNorm c a y := by
  have hn (z : Plane) : 0 ≤ rawNorm c a z := by
    simp only [rawNorm]
    split_ifs
    · exact le_rfl
    · exact hc
    · exact zero_le_one
  exact (rawNorm_add_le_max hc hc1 a x y).trans (max_le (by linarith [hn y])
    (by linarith [hn x]))

open Classical in
theorem rawNorm_smul (c : ℝ) (a q : ℚ) (x : Plane) :
    rawNorm c a (q • x) = (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ) q *
      rawNorm c a x := by
  by_cases hq : q = 0
  · simp [hq]
  rw [AbsoluteValue.trivial_apply hq, one_mul]
  by_cases hx : x = 0
  · simp [hx]
  have hqx : q • x ≠ 0 := (smul_eq_zero_iff_right hq).not.mpr hx
  have hline : q * x.2 = a * (q * x.1) ↔ x.2 = a * x.1 := by
    rw [mul_left_comm a q x.1]
    exact ⟨mul_left_cancel₀ hq, fun h ↦ congrArg (q * ·) h⟩
  simp only [rawNorm, ite_eq_right hqx, ite_eq_right hx, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, hline]

open Classical in
/-- The source's generic weighted line norm over the trivial rational field. -/
def localSeminorm (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (a : ℚ) :
    Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ)) Plane :=
  Seminorm.of (rawNorm c a) (rawNorm_add_le hc.le hc1 a) (by
    intro q x
    change rawNorm c a (q.ofAbs • x) = ‖q‖ * rawNorm c a x
    rw [WithAbs.norm_eq_apply_ofAbs]
    exact rawNorm_smul c a q.ofAbs x)

open Classical in
/-- The generic norm on all actual completed counting fibres. -/
def normFamily (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) : NormFamily countingCurve Plane where
  norm a := by
    change Seminorm (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ).Completion
      ((AbsoluteValue.trivial : AbsoluteValue ℚ ℝ).Completion ⊗[ℚ] Plane)
    exact Seminorm.of
      (fun z ↦ localSeminorm c hc hc1 a (trivialCompletedTensorEquiv ℚ Plane z))
      (by
        intro x y
        rw [map_add]
        exact map_add_le_add (localSeminorm c hc hc1 a) _ _)
      (by
        intro q z
        rw [trivialCompletedTensorEquiv_smul]
        change localSeminorm c hc hc1 a
          (WithAbs.toAbs (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ)
            (trivialCompletionAlgEquiv ℚ q) • trivialCompletedTensorEquiv ℚ Plane z) = _
        rw [map_smul_eq_mul, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_toAbs,
          ← norm_trivialCompletion ℚ q])
  norm_eq_zero_iff a z := by
    change rawNorm c a (trivialCompletedTensorEquiv ℚ Plane z) = 0 ↔ z = 0
    rw [rawNorm_eq_zero_iff hc, LinearEquiv.map_eq_zero_iff]

open Classical in
/-- This formula covers every completed vector. -/
theorem normFamily_norm (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (a : countingCurve.Ω)
    (z : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) :
    (normFamily c hc hc1).norm a z = rawNorm c a (trivialCompletedTensorEquiv ℚ Plane z) := rfl

open Classical in
@[simp]
theorem normFamily_norm_rational (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (a : countingCurve.Ω) (x : Plane) :
    (normFamily c hc hc1).norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] x) =
      rawNorm c a x := by
  rw [normFamily_norm, trivialCompletedTensorEquiv_one_tmul]

/-- The actual family is ultrametric on every completed finite fibre. -/
theorem normFamily_isUltrametric (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (normFamily c hc hc1).IsUltrametric := by
  constructor
  intro a _ x y
  rw [normFamily_norm, normFamily_norm, normFamily_norm, map_add]
  exact rawNorm_add_le_max hc.le hc1 a _ _

open Classical in
/-- The generic lower bound holds on every actual nonzero completed tensor. -/
theorem normFamily_cost_le (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (a : countingCurve.Ω) {z : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane} (hz : z ≠ 0) :
    c ≤ (normFamily c hc hc1).norm a z := by
  rw [normFamily_norm]
  exact cost_le_rawNorm hc1 a ((LinearEquiv.map_eq_zero_iff _).not.mpr hz)

/-- The completed generic norm is at most one at every vector. -/
theorem normFamily_norm_le_one (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (a : countingCurve.Ω) (z : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) :
    (normFamily c hc hc1).norm a z ≤ 1 :=
  rawNorm_le_one hc1 a _

open Classical in
/-- Exact weighted coordinates; no local value-group realization of the cost is used. -/
theorem rawNorm_weighted_coordinates (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (a : ℚ) (x : Plane) :
    rawNorm c a x = max
      (c * (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ) x.1)
      ((AbsoluteValue.trivial : AbsoluteValue ℚ ℝ) (x.2 - a * x.1)) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hline : x.2 = a * x.1
  · have hx1 : x.1 ≠ 0 := by
      intro hz
      have hx2 : x.2 = 0 := by simpa only [hz, mul_zero] using hline
      exact hx (Prod.ext hz hx2)
    rw [rawNorm, ite_eq_right hx, ite_eq_left hline, AbsoluteValue.trivial_apply hx1]
    simp [hline, max_eq_left hc.le]
  · have hdiff : x.2 - a * x.1 ≠ 0 := sub_ne_zero.mpr hline
    rw [rawNorm, ite_eq_right hx, ite_eq_right hline, AbsoluteValue.trivial_apply hdiff]
    by_cases hx1 : x.1 = 0
    · simp [hx1]
    · rw [AbsoluteValue.trivial_apply hx1, mul_one, max_eq_right hc1]

/-- The actual rational coordinate shear whose first inverse basis vector is cheap. -/
def cheapCoordinateEquiv (a : ℚ) : Plane ≃ₗ[ℚ] Plane where
  toFun x := (x.1, x.2 - a * x.1)
  invFun x := (x.1, x.2 + a * x.1)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by
    ext <;> dsimp
    ring
  map_smul' q x := by
    ext <;> dsimp [smul_eq_mul]
    ring

/-- The explicit rational cheap/complement basis, before genuine base change. -/
def cheapBasis (a : ℚ) : Module.Basis (Fin 2) ℚ Plane :=
  (Module.Basis.finTwoProd ℚ).map (cheapCoordinateEquiv a).symm

@[simp]
theorem cheapBasis_zero (a : ℚ) : cheapBasis a 0 = ((1, a) : Plane) := by
  simp [cheapBasis, cheapCoordinateEquiv]

@[simp]
theorem cheapBasis_one (a : ℚ) : cheapBasis a 1 = ((0, 1) : Plane) := by
  simp [cheapBasis, cheapCoordinateEquiv]

@[simp]
theorem cheapBasis_equivFun_zero (a : ℚ) (x : Plane) :
    (cheapBasis a).equivFun x 0 = x.1 := by
  simp [cheapBasis, cheapCoordinateEquiv, Module.Basis.equivFun_apply]

@[simp]
theorem cheapBasis_equivFun_one (a : ℚ) (x : Plane) :
    (cheapBasis a).equivFun x 1 = x.2 - a * x.1 := by
  simp [cheapBasis, cheapCoordinateEquiv, Module.Basis.equivFun_apply]

open Classical in
/-- Exact weighted orthogonality on every genuine completed fibre. -/
theorem normFamily_weighted_basis (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (a : countingCurve.Ω) (z : (countingCurve.ϕ a).Completion ⊗[ℚ] Plane) :
    (normFamily c hc hc1).norm a z = max
      (c * ‖((cheapBasis a).baseChange (countingCurve.ϕ a).Completion).equivFun z 0‖)
      ‖((cheapBasis a).baseChange (countingCurve.ϕ a).Completion).equivFun z 1‖ := by
  rw [completed_eq_one_tmul a z, normFamily_norm_rational,
    rawNorm_weighted_coordinates c hc hc1]
  simp only [NormFamily.basis_equivFun_one_tmul (S := countingCurve), cheapBasis_equivFun_zero,
    cheapBasis_equivFun_one, countingCurve.norm_algebraMap_eq_absValue]

open Classical in
@[simp]
theorem normFamily_norm_cheap_basis (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (a : countingCurve.Ω) :
    (normFamily c hc hc1).norm a
      (((cheapBasis a).baseChange (countingCurve.ϕ a).Completion) 0) = c := by
  rw [Module.Basis.baseChange_apply, normFamily_norm_rational]
  simp [cheapBasis_zero, rawNorm]

open Classical in
@[simp]
theorem normFamily_norm_complement_basis (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (a : countingCurve.Ω) :
    (normFamily c hc hc1).norm a
      (((cheapBasis a).baseChange (countingCurve.ϕ a).Completion) 1) = 1 := by
  rw [Module.Basis.baseChange_apply, normFamily_norm_rational]
  simp [cheapBasis_one, rawNorm]

end

end ArakelovGeometry.MinkowskiCounting

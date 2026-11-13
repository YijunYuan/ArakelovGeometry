/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Determinant.Bound
import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The upper dual slope inequality

The actual dual norm of a restriction is bounded by the quotient norm of the
ambient dual, even when equality is unavailable. The quotient-mean formula
and sharp determinant degree-duality defect prove source Corollary 4.3.27.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

/-- Every extension has norm at least the actual restricted functional.
Taking the infimum over all completed extensions proves the comparison,
without a local extension theorem or ultrametric hypothesis. -/
theorem restrict_dual_norm_le_dual_pushforward (ξ : NormFamily S E)
    (U : Submodule K E) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K U) :
    (ξ.restrict U).dual.norm ω z ≤
      (ξ.dual.pushforward U.subtype.dualMap
        (LinearMap.dualMap_surjective_of_injective U.subtype_injective)).norm ω z := by
  apply (ξ.dual.le_quotientSeminorm_iff U.subtype.dualMap
    (LinearMap.dualMap_surjective_of_injective U.subtype_injective) ω z _).mpr
  intro x hx
  rw [← hx]
  exact ξ.pullback_dual_norm_le U.subtype U.subtype_injective ω x

end NormFamily

namespace AdelicVectorBundle

variable [S.IsProper]

/-- The quotient norm on the actual subspace dual has degree at most
the degree of its actual restricted-space dual norm. -/
theorem degree_dual_pushforward_restriction_le (V : AdelicVectorBundle S)
    (U : Submodule K V)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hm : ((V.dualOfMeasurableBase).toNormFamily.pushforward U.subtype.dualMap
      (LinearMap.dualMap_surjective_of_injective U.subtype_injective)).IsMeasurable] :
    ((V.dualOfMeasurableBase).pushforward U.subtype.dualMap
      (LinearMap.dualMap_surjective_of_injective U.subtype_injective)).degree ≤
        ((V.restrictOfMeasurableBase U).dualOfMeasurableBase).degree := by
  apply degree_antitone (V.restrictOfMeasurableBase U).dualOfMeasurableBase
    ((V.dualOfMeasurableBase).pushforward U.subtype.dualMap
      (LinearMap.dualMap_surjective_of_injective U.subtype_injective)).toNormFamily
    (hW := ((V.dualOfMeasurableBase).pushforward U.subtype.dualMap
      (LinearMap.dualMap_surjective_of_injective U.subtype_injective)).toIsAdelic)
  intro ω z
  exact V.toNormFamily.restrict_dual_norm_le_dual_pushforward U ω z

/-- The source quotient-mean formula, followed by actual norm comparison,
bounds the ambient dual minimum by each nonzero restricted-space dual mean. -/
theorem minimalSlope_dual_le_slope_dual_restrict (V : AdelicVectorBundle S)
    (U : Submodule K V) (hU : 0 < Module.finrank K U)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.dualOfMeasurableBase).minimalSlope ≤
      (((V.restrictOfMeasurableBase U).dualOfMeasurableBase).slope : EReal) := by
  let D := V.dualOfMeasurableBase
  let p := U.subtype.dualMap
  let hp := LinearMap.dualMap_surjective_of_injective U.subtype_injective
  let hm := D.isMeasurable.pushforward_of_discrete_or_countable p hp
  have hr : 0 < Module.finrank K (Module.Dual K U) := by
    rwa [Subspace.dual_finrank_eq]
  have hq := D.minimalSlope_le_slope_pushforward p hp (hm := hm) hr
  refine hq.trans (EReal.coe_le_coe_iff.mpr ?_)
  apply div_le_div_of_nonneg_right (V.degree_dual_pushforward_restriction_le U (hm := hm))
    (Nat.cast_nonneg (Module.finrank K (Module.Dual K U)))

/-- Dividing the sharp actual determinant degree-duality defect by
the positive rank gives the sharp source mean-slope bound. -/
theorem slope_add_slope_dual_le_half_log_rank (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V) :
    V.slope + (V.dualOfMeasurableBase).slope ≤
      (1 / 2 : ℝ) * Real.log (Module.finrank K V) * (S.v S.Ωinf).toReal := by
  have hd := V.degree_add_degree_dual_le
  rw [V.degree_eq_rank_mul_slope,
    (V.dualOfMeasurableBase).degree_eq_rank_mul_slope,
    Subspace.dual_finrank_eq] at hd
  have hp : (0 : ℝ) < Module.finrank K V := Nat.cast_pos.mpr hr
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

/-- The vanishing actual Hermitian determinant discrepancy gives exact
duality of the real mean slopes, including their zero-rank convention. -/
theorem slope_add_slope_dual_eq_zero_of_isHermitian (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    V.slope + (V.dualOfMeasurableBase).slope = 0 := by
  have hd : V.degree + (V.dualOfMeasurableBase).degree = 0 := by
    rw [← V.determinantDiscrepancy_eq_degree_add_degree_dual]
    exact V.determinantDiscrepancy_eq_zero_of_isHermitian
  rw [slope, slope, Subspace.dual_finrank_eq, ← add_div, hd, zero_div]

/-- Source Corollary 4.3.27, equation (4.48), for the actual source
maximal and minimal slopes. Positive rank is essential to the statement. -/
theorem minimalSlope_dual_add_maximalSlope_le_half_log_rank (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V) :
    (V.dualOfMeasurableBase).minimalSlope + V.maximalSlope ≤
      ((1 / 2 : ℝ) * Real.log (Module.finrank K V) * (S.v S.Ωinf).toReal : EReal) := by
  have hrD : 0 < Module.finrank K (Module.Dual K V) := by
    rwa [Subspace.dual_finrank_eq]
  obtain ⟨a, ha⟩ := (V.dualOfMeasurableBase).exists_minimalSlope_eq_coe hrD
  let C := (1 / 2 : ℝ) * Real.log (Module.finrank K V) * (S.v S.Ωinf).toReal
  have hmax : V.maximalSlope ≤ ((C - a : ℝ) : EReal) := by
    apply V.maximalSlope_le
    intro U hU
    have hm := V.minimalSlope_dual_le_slope_dual_restrict U hU
    rw [ha, EReal.coe_le_coe_iff] at hm
    have hd := (V.restrictOfMeasurableBase U).slope_add_slope_dual_le_half_log_rank
      hU
    have hl : (1 / 2 : ℝ) * Real.log (Module.finrank K U) * (S.v S.Ωinf).toReal ≤ C := by
      have hlog := Real.log_le_log (Nat.cast_pos.mpr hU) (Nat.cast_le.mpr U.finrank_le)
      dsimp only [C]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 1 / 2))
        ENNReal.toReal_nonneg
    apply EReal.coe_le_coe_iff.mpr
    linarith
  rw [ha]
  calc
    (a : EReal) + V.maximalSlope ≤ (a : EReal) + ((C - a : ℝ) : EReal) :=
      add_le_add le_rfl hmax
    _ = (C : EReal) := by rw [← EReal.coe_add, add_sub_cancel]

/-- Canonical completed biduality for an actual ultrametric norm family
preserves its maximal slope. In particular this applies to Hermitian bundles. -/
theorem maximalSlope_dual_dual_eq_of_isUltrametric (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametric] :
    ((V.dualOfMeasurableBase).dualOfMeasurableBase).maximalSlope =
      V.maximalSlope := by
  symm
  apply V.maximalSlope_eq_of_completed_isometry _ (Module.evalEquiv K V)
  intro ω x
  simp only [Module.evalEquiv_toLinearMap]
  by_cases hω : ω ∈ S.Ωfin
  · exact hV.dual_dual_norm_eval ω hω x
  · exact V.toNormFamily.dual_dual_norm_eval_eq_of_isRCLike ω (hN ω hω) x

/-- The exact Hermitian clause of source Corollary 4.3.27: the source
dual minimum and primal maximum have zero sum in positive rank. -/
theorem minimalSlope_dual_add_maximalSlope_eq_zero_of_isHermitian
    (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V) :
    (V.dualOfMeasurableBase).minimalSlope + V.maximalSlope = 0 := by
  have hrD : 0 < Module.finrank K (Module.Dual K V) := by
    rwa [Subspace.dual_finrank_eq]
  obtain ⟨a, ha⟩ := (V.dualOfMeasurableBase).exists_minimalSlope_eq_coe hrD
  have hmax : V.maximalSlope ≤ ((-a : ℝ) : EReal) := by
    apply V.maximalSlope_le
    intro U hU
    have hm := V.minimalSlope_dual_le_slope_dual_restrict U hU
    rw [ha, EReal.coe_le_coe_iff] at hm
    have hd := (V.restrictOfMeasurableBase U).slope_add_slope_dual_eq_zero_of_isHermitian
      (hV := (hV.restrict U))
    apply EReal.coe_le_coe_iff.mpr
    linarith
  have hupper : (V.dualOfMeasurableBase).minimalSlope +
      V.maximalSlope ≤ 0 := by
    rw [ha]
    calc
      (a : EReal) + V.maximalSlope ≤ (a : EReal) + ((-a : ℝ) : EReal) :=
        add_le_add le_rfl hmax
      _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  have hlower := (V.dualOfMeasurableBase).minimalSlope_add_maximalSlope_dual_nonneg
    hrD
  rw [V.maximalSlope_dual_dual_eq_of_isUltrametric] at hlower
  exact le_antisymm hupper hlower

end AdelicVectorBundle

end

end ArakelovGeometry

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
theorem degree_dual_pushforward_restriction_le (V : AdelicVectorBundle S E)
    (U : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hm : ((V.dualOfMeasurableBase hS).toNormFamily.pushforward U.subtype.dualMap
      (LinearMap.dualMap_surjective_of_injective U.subtype_injective)).IsMeasurable) :
    ((V.dualOfMeasurableBase hS).pushforward U.subtype.dualMap
      (LinearMap.dualMap_surjective_of_injective U.subtype_injective) hm).degree hS hN ≤
        ((V.restrictOfMeasurableBase U hS).dualOfMeasurableBase hS).degree hS hN := by
  apply degree_antitone _ _ hS hN
  intro ω z
  exact V.toNormFamily.restrict_dual_norm_le_dual_pushforward U ω z

/-- The source quotient-mean formula, followed by actual norm comparison,
bounds the ambient dual minimum by each nonzero restricted-space dual mean. -/
theorem minimalSlope_dual_le_slope_dual_restrict (V : AdelicVectorBundle S E)
    (U : Submodule K E) (hU : 0 < Module.finrank K U)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.dualOfMeasurableBase hS).minimalSlope hS hN ≤
      (((V.restrictOfMeasurableBase U hS).dualOfMeasurableBase hS).slope hS hN : EReal) := by
  let D := V.dualOfMeasurableBase hS
  let p := U.subtype.dualMap
  let hp := LinearMap.dualMap_surjective_of_injective U.subtype_injective
  let hm := D.isMeasurable.pushforward_of_discrete_or_countable hS p hp
  have hr : 0 < Module.finrank K (Module.Dual K U) := by
    rwa [Subspace.dual_finrank_eq]
  have hq := D.minimalSlope_le_slope_pushforward p hp hm hr hS hN
  refine hq.trans (EReal.coe_le_coe_iff.mpr ?_)
  apply div_le_div_of_nonneg_right (V.degree_dual_pushforward_restriction_le U hS hN hm)
    (Nat.cast_nonneg (Module.finrank K (Module.Dual K U)))

/-- Dividing the sharp actual determinant degree-duality defect by
the positive rank gives the sharp source mean-slope bound. -/
theorem slope_add_slope_dual_le_half_log_rank (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E) :
    V.slope hS hN + (V.dualOfMeasurableBase hS).slope hS hN ≤
      (1 / 2 : ℝ) * Real.log (Module.finrank K E) * (S.v S.Ωinf).toReal := by
  have hd := V.degree_add_degree_dual_le hS hN
  rw [V.degree_eq_rank_mul_slope hS hN,
    (V.dualOfMeasurableBase hS).degree_eq_rank_mul_slope hS hN,
    Subspace.dual_finrank_eq] at hd
  have hp : (0 : ℝ) < Module.finrank K E := Nat.cast_pos.mpr hr
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

/-- The vanishing actual Hermitian determinant discrepancy gives exact
duality of the real mean slopes, including their zero-rank convention. -/
theorem slope_add_slope_dual_eq_zero_of_isHermitian (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    V.slope hS hN + (V.dualOfMeasurableBase hS).slope hS hN = 0 := by
  have hd : V.degree hS hN + (V.dualOfMeasurableBase hS).degree hS hN = 0 := by
    rw [← V.determinantDiscrepancy_eq_degree_add_degree_dual hS hN]
    exact V.determinantDiscrepancy_eq_zero_of_isHermitian hN hV
  rw [slope, slope, Subspace.dual_finrank_eq, ← add_div, hd, zero_div]

/-- Source Corollary 4.3.27, equation (4.48), for the actual source
maximal and minimal slopes. Positive rank is essential to the statement. -/
theorem minimalSlope_dual_add_maximalSlope_le_half_log_rank (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E) :
    (V.dualOfMeasurableBase hS).minimalSlope hS hN + V.maximalSlope hS hN ≤
      ((1 / 2 : ℝ) * Real.log (Module.finrank K E) * (S.v S.Ωinf).toReal : EReal) := by
  have hrD : 0 < Module.finrank K (Module.Dual K E) := by
    rwa [Subspace.dual_finrank_eq]
  obtain ⟨a, ha⟩ := (V.dualOfMeasurableBase hS).exists_minimalSlope_eq_coe hS hN hrD
  let C := (1 / 2 : ℝ) * Real.log (Module.finrank K E) * (S.v S.Ωinf).toReal
  have hmax : V.maximalSlope hS hN ≤ ((C - a : ℝ) : EReal) := by
    apply V.maximalSlope_le hS hN
    intro U hU
    have hm := V.minimalSlope_dual_le_slope_dual_restrict U hU hS hN
    rw [ha, EReal.coe_le_coe_iff] at hm
    have hd := (V.restrictOfMeasurableBase U hS).slope_add_slope_dual_le_half_log_rank
      hS hN hU
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
    (a : EReal) + V.maximalSlope hS hN ≤ (a : EReal) + ((C - a : ℝ) : EReal) :=
      add_le_add le_rfl hmax
    _ = (C : EReal) := by rw [← EReal.coe_add, add_sub_cancel]

/-- Canonical completed biduality for an actual ultrametric norm family
preserves its maximal slope. In particular this applies to Hermitian bundles. -/
theorem maximalSlope_dual_dual_eq_of_isUltrametric (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsUltrametric) :
    ((V.dualOfMeasurableBase hS).dualOfMeasurableBase hS).maximalSlope hS hN =
      V.maximalSlope hS hN := by
  symm
  apply V.maximalSlope_eq_of_completed_isometry _ (Module.evalEquiv K E) hS hN
  intro ω x
  simp only [dualOfMeasurableBase_toNormFamily, Module.evalEquiv_toLinearMap]
  by_cases hω : ω ∈ S.Ωfin
  · exact hV.dual_dual_norm_eval ω hω x
  · exact V.toNormFamily.dual_dual_norm_eval_eq_of_isRCLike ω (hN ω hω) x

/-- The exact Hermitian clause of source Corollary 4.3.27: the source
dual minimum and primal maximum have zero sum in positive rank. -/
theorem minimalSlope_dual_add_maximalSlope_eq_zero_of_isHermitian
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hr : 0 < Module.finrank K E) :
    (V.dualOfMeasurableBase hS).minimalSlope hS hN + V.maximalSlope hS hN = 0 := by
  have hrD : 0 < Module.finrank K (Module.Dual K E) := by
    rwa [Subspace.dual_finrank_eq]
  obtain ⟨a, ha⟩ := (V.dualOfMeasurableBase hS).exists_minimalSlope_eq_coe hS hN hrD
  have hmax : V.maximalSlope hS hN ≤ ((-a : ℝ) : EReal) := by
    apply V.maximalSlope_le hS hN
    intro U hU
    have hm := V.minimalSlope_dual_le_slope_dual_restrict U hU hS hN
    rw [ha, EReal.coe_le_coe_iff] at hm
    have hd := (V.restrictOfMeasurableBase U hS).slope_add_slope_dual_eq_zero_of_isHermitian
      hS hN (hV.restrict U)
    apply EReal.coe_le_coe_iff.mpr
    linarith
  have hupper : (V.dualOfMeasurableBase hS).minimalSlope hS hN +
      V.maximalSlope hS hN ≤ 0 := by
    rw [ha]
    calc
      (a : EReal) + V.maximalSlope hS hN ≤ (a : EReal) + ((-a : ℝ) : EReal) :=
        add_le_add le_rfl hmax
      _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  have hlower := (V.dualOfMeasurableBase hS).minimalSlope_add_maximalSlope_dual_nonneg
    hS hN hrD
  rw [V.maximalSlope_dual_dual_eq_of_isUltrametric hS hN hV.1] at hlower
  exact le_antisymm hupper hlower

end AdelicVectorBundle

end

end ArakelovGeometry

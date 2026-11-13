/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Pair
public import ArakelovGeometry.AdelicVectorBundle.Minkowski.Basic

import ArakelovGeometry.AdelicVectorBundle.Dual.BidualQuotient
import ArakelovGeometry.AdelicVectorBundle.Slope.DualUpper
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import ArakelovGeometry.AdelicVectorBundle.Tensor.DualNorm
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The mixed tensor lower slope bound from an ordinary Minkowski level

Canonical completed mixed-tensor duality applies the ordinary Minkowski
predicate to the two actual dual bundles. Bidual minimal-slope invariance
and the sharp dual slope defect remove the dual factors. No ultrametricity
premise is imposed on either original bundle.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

universe u v w wF

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} {F : Type wF} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The true minimum of the double dual equals the original minimum,
without equality of the original norm family with its bidual. -/
theorem minimalSlope_dual_dual_eq (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    ((V.dualOfNormMeasurability).dualOfNormMeasurability).minimalSlope =
      V.minimalSlope := by
  have hi := (V.bidualOfNormMeasurability).minimalSlope_eq_of_completed_isometry
    ((V.dualOfNormMeasurability).dualOfNormMeasurability) (Module.evalEquiv K V)
    (by
      intro ω x
      simp only [NormFamily.pullback_norm, Module.evalEquiv_toLinearMap])
  rw [V.minimalSlope_bidualOfNormMeasurability] at hi
  exact hi.symm

/-- Apply the sharp dual slope defect to the actual dual, then use bidual
minimal-slope invariance. The original norms need not be ultrametric. -/
theorem minimalSlope_add_maximalSlope_dual_le_half_log_rank (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V) :
    V.minimalSlope + (V.dualOfNormMeasurability).maximalSlope ≤
      ((1 / 2 : ℝ) * Real.log (Module.finrank K V) * (S.v S.Ωinf).toReal : EReal) := by
  have hrD : 0 < Module.finrank K (Module.Dual K V) := by
    rwa [Subspace.dual_finrank_eq]
  have h := (V.dualOfNormMeasurability).minimalSlope_dual_add_maximalSlope_le_half_log_rank
    hrD
  rwa [V.minimalSlope_dual_dual_eq, Subspace.dual_finrank_eq] at h

/-- Actual completed mixed-tensor duality transports the true maximal slope
through the canonical algebraic dual distribution equivalence. -/
theorem maximalSlope_dual_mixedTensorPair_eq_injective_dual
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    ((V.mixedTensorPair W).dualOfNormMeasurability).maximalSlope =
      ((V.dualOfNormMeasurability).injectiveTensorPair (W.dualOfNormMeasurability)
).maximalSlope := by
  symm
  apply maximalSlope_eq_of_completed_isometry _ _ (TensorProduct.dualDistribEquiv K V W)
  intro ω x
  simp only [TensorProduct.toLinearMap_dualDistribEquiv]
  exact V.toNormFamily.mixedTensorPair_dual_norm_eq_injective W.toNormFamily ω x

/-- Source Corollary 4.3.76(2), on arbitrary positive-rank actual factors.
Only the actual dual families must be ultrametric, and this is produced.
The ordinary global Minkowski predicate is applied to their actual tensor,
in the containing universe `max u w wF` of the scalar field and factor spaces. -/
theorem minimalSlope_mixedTensorPair_ge_of_minkowski
    (V : AdelicVectorBundle.{w} S) (W : AdelicVectorBundle.{wF} S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    {C : ℝ} (hM : S.HasMinkowskiPropertyAtLevel.{u, v, max u w wF} C)
    (hE : 0 < Module.finrank K V) (hF : 0 < Module.finrank K W) :
    V.minimalSlope + W.minimalSlope -
      ((C + (S.v S.Ωinf).toReal / 2) *
        Real.log ((Module.finrank K V : ℝ) * Module.finrank K W) : ℝ) ≤
          (V.mixedTensorPair W).minimalSlope := by
  let T := V.mixedTensorPair W
  have hrT : 0 < Module.finrank K (V ⊗[K] W) := by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos hE hF
  have hrE : 0 < Module.finrank K (Module.Dual K V) := by
    rwa [Subspace.dual_finrank_eq]
  have hrF : 0 < Module.finrank K (Module.Dual K W) := by
    rwa [Subspace.dual_finrank_eq]
  have hmax := maximalSlope_injectiveTensorPair_le_of_minkowski
    (V.dualOfNormMeasurability) (W.dualOfNormMeasurability)
    (hV := V.toNormFamily.dual_isUltrametricAtFinitePlaces)
      (hW := W.toNormFamily.dual_isUltrametricAtFinitePlaces)
    hM hrE hrF
  rw [← V.maximalSlope_dual_mixedTensorPair_eq_injective_dual W,
    Subspace.dual_finrank_eq, Subspace.dual_finrank_eq] at hmax
  have hlow := T.minimalSlope_add_maximalSlope_dual_nonneg hrT
  have hV := V.minimalSlope_add_maximalSlope_dual_le_half_log_rank hE
  have hW := W.minimalSlope_add_maximalSlope_dual_le_half_log_rank hF
  obtain ⟨a, ha⟩ := V.exists_minimalSlope_eq_coe hE
  obtain ⟨b, hb⟩ := W.exists_minimalSlope_eq_coe hF
  obtain ⟨c, hc⟩ := T.exists_minimalSlope_eq_coe hrT
  obtain ⟨d, hd⟩ := (V.dualOfNormMeasurability).exists_maximalSlope_eq_coe hrE
  obtain ⟨e, he⟩ := (W.dualOfNormMeasurability).exists_maximalSlope_eq_coe hrF
  have hrTD : 0 < Module.finrank K (Module.Dual K (V ⊗[K] W)) := by
    rwa [Subspace.dual_finrank_eq]
  obtain ⟨f, hf⟩ := (T.dualOfNormMeasurability).exists_maximalSlope_eq_coe hrTD
  change (T.dualOfNormMeasurability).maximalSlope ≤ _ at hmax
  rw [hf, hd, he, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hmax
  rw [hc, hf, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_le_coe_iff] at hlow
  rw [ha, hd, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul,
    EReal.coe_le_coe_iff] at hV
  rw [hb, he, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul,
    EReal.coe_le_coe_iff] at hW
  change _ ≤ T.minimalSlope
  rw [ha, hb, hc, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  rw [Real.log_mul (Nat.cast_ne_zero.mpr hE.ne') (Nat.cast_ne_zero.mpr hF.ne')] at hmax ⊢
  nlinarith

/-- A zero left factor has zero tensor rank, so its actual minimum is top.
This uses no global Minkowski property or positive-rank logarithm. -/
theorem minimalSlope_mixedTensorPair_eq_top_of_left_finrank_eq_zero
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hE : Module.finrank K V = 0) :
    (V.mixedTensorPair W).minimalSlope = ⊤ := by
  apply minimalSlope_eq_top_of_finrank_eq_zero
  simp only [Module.finrank_tensorProduct, hE, zero_mul]

/-- The opposite zero-factor orientation has the same actual top minimum. -/
theorem minimalSlope_mixedTensorPair_eq_top_of_right_finrank_eq_zero
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (hF : Module.finrank K W = 0) :
    (V.mixedTensorPair W).minimalSlope = ⊤ := by
  apply minimalSlope_eq_top_of_finrank_eq_zero
  simp only [Module.finrank_tensorProduct, hF, mul_zero]

end ArakelovGeometry.AdelicVectorBundle

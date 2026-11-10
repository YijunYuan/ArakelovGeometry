/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.Minkowski
import ArakelovGeometry.AdelicVectorBundle.BundleTensorPair
import ArakelovGeometry.AdelicVectorBundle.TensorDualNorm
import ArakelovGeometry.AdelicVectorBundle.BidualQuotient

/-!
# The mixed tensor lower slope bound from an ordinary Minkowski level

Canonical completed mixed-tensor duality applies the ordinary Minkowski
predicate to the two actual dual bundles. Bidual minimal-slope invariance
and the sharp dual slope defect remove the dual factors. No ultrametricity
premise is imposed on either original bundle.
-/

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E F : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The true minimum of the double dual equals the original minimum,
without equality of the original norm family with its bidual. -/
theorem minimalSlope_dual_dual_eq (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.dualOfMeasurableBase hS).dualOfMeasurableBase hS).minimalSlope hS hN =
      V.minimalSlope hS hN := by
  have hi := (V.bidualOfMeasurableBase hS).minimalSlope_eq_of_completed_isometry
    ((V.dualOfMeasurableBase hS).dualOfMeasurableBase hS) (Module.evalEquiv K E)
    hS hN (by
      intro ω x
      simp only [bidualOfMeasurableBase_toNormFamily,
        dualOfMeasurableBase_toNormFamily, NormFamily.pullback_norm,
        Module.evalEquiv_toLinearMap])
  rw [V.minimalSlope_bidualOfMeasurableBase hS hN] at hi
  exact hi.symm

/-- Apply the sharp dual slope defect to the actual dual, then use bidual
minimal-slope invariance. The original norms need not be ultrametric. -/
theorem minimalSlope_add_maximalSlope_dual_le_half_log_rank (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E) :
    V.minimalSlope hS hN + (V.dualOfMeasurableBase hS).maximalSlope hS hN ≤
      ((1 / 2 : ℝ) * Real.log (Module.finrank K E) * (S.v S.Ωinf).toReal : EReal) := by
  have hrD : 0 < Module.finrank K (Module.Dual K E) := by
    rwa [Subspace.dual_finrank_eq]
  have h := (V.dualOfMeasurableBase hS).minimalSlope_dual_add_maximalSlope_le_half_log_rank
    hS hN hrD
  rwa [V.minimalSlope_dual_dual_eq hS hN, Subspace.dual_finrank_eq] at h

/-- Actual completed mixed-tensor duality transports the true maximal slope
through the canonical algebraic dual distribution equivalence. -/
theorem maximalSlope_dual_mixedTensorPair_eq_injective_dual
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.mixedTensorPair W hS hN).dualOfMeasurableBase hS).maximalSlope hS hN =
      ((V.dualOfMeasurableBase hS).injectiveTensorPair (W.dualOfMeasurableBase hS)
        hS hN).maximalSlope hS hN := by
  symm
  apply maximalSlope_eq_of_completed_isometry _ _ (TensorProduct.dualDistribEquiv K E F)
    hS hN
  intro ω x
  simp only [dualOfMeasurableBase_toNormFamily, mixedTensorPair_toNormFamily,
    injectiveTensorPair_toNormFamily]
  exact V.toNormFamily.mixedTensorPair_dual_norm_eq_injective W.toNormFamily ω x

/-- Source Corollary 4.3.76(2), on arbitrary positive-rank actual factors.
Only the actual dual families must be ultrametric, and this is produced.
The ordinary global Minkowski predicate is applied to their actual tensor,
in the containing universe `max u w` of the scalar field and factor spaces. -/
theorem minimalSlope_mixedTensorPair_ge_of_minkowski
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {C : ℝ} (hM : S.HasMinkowskiPropertyAtLevel.{u, v, max u w} hS hN C)
    (hE : 0 < Module.finrank K E) (hF : 0 < Module.finrank K F) :
    V.minimalSlope hS hN + W.minimalSlope hS hN -
      ((C + (S.v S.Ωinf).toReal / 2) *
        Real.log ((Module.finrank K E : ℝ) * Module.finrank K F) : ℝ) ≤
          (V.mixedTensorPair W hS hN).minimalSlope hS hN := by
  let T := V.mixedTensorPair W hS hN
  have hrT : 0 < Module.finrank K (E ⊗[K] F) := by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos hE hF
  have hrE : 0 < Module.finrank K (Module.Dual K E) := by
    rwa [Subspace.dual_finrank_eq]
  have hrF : 0 < Module.finrank K (Module.Dual K F) := by
    rwa [Subspace.dual_finrank_eq]
  have hmax := maximalSlope_injectiveTensorPair_le_of_minkowski
    (V.dualOfMeasurableBase hS) (W.dualOfMeasurableBase hS)
    V.toNormFamily.dual_isUltrametric W.toNormFamily.dual_isUltrametric
    hS hN hM hrE hrF
  rw [← V.maximalSlope_dual_mixedTensorPair_eq_injective_dual W hS hN,
    Subspace.dual_finrank_eq, Subspace.dual_finrank_eq] at hmax
  have hlow := T.minimalSlope_add_maximalSlope_dual_nonneg hS hN hrT
  have hV := V.minimalSlope_add_maximalSlope_dual_le_half_log_rank hS hN hE
  have hW := W.minimalSlope_add_maximalSlope_dual_le_half_log_rank hS hN hF
  obtain ⟨a, ha⟩ := V.exists_minimalSlope_eq_coe hS hN hE
  obtain ⟨b, hb⟩ := W.exists_minimalSlope_eq_coe hS hN hF
  obtain ⟨c, hc⟩ := T.exists_minimalSlope_eq_coe hS hN hrT
  obtain ⟨d, hd⟩ := (V.dualOfMeasurableBase hS).exists_maximalSlope_eq_coe hS hN hrE
  obtain ⟨e, he⟩ := (W.dualOfMeasurableBase hS).exists_maximalSlope_eq_coe hS hN hrF
  have hrTD : 0 < Module.finrank K (Module.Dual K (E ⊗[K] F)) := by
    rwa [Subspace.dual_finrank_eq]
  obtain ⟨f, hf⟩ := (T.dualOfMeasurableBase hS).exists_maximalSlope_eq_coe hS hN hrTD
  change (T.dualOfMeasurableBase hS).maximalSlope hS hN ≤ _ at hmax
  rw [hf, hd, he, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hmax
  rw [hc, hf, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_le_coe_iff] at hlow
  rw [ha, hd, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul,
    EReal.coe_le_coe_iff] at hV
  rw [hb, he, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul,
    EReal.coe_le_coe_iff] at hW
  change _ ≤ T.minimalSlope hS hN
  rw [ha, hb, hc, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  rw [Real.log_mul (Nat.cast_ne_zero.mpr hE.ne') (Nat.cast_ne_zero.mpr hF.ne')] at hmax ⊢
  nlinarith

/-- A zero left factor has zero tensor rank, so its actual minimum is top.
This uses no global Minkowski property or positive-rank logarithm. -/
theorem minimalSlope_mixedTensorPair_eq_top_of_left_finrank_eq_zero
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hE : Module.finrank K E = 0) :
    (V.mixedTensorPair W hS hN).minimalSlope hS hN = ⊤ := by
  apply minimalSlope_eq_top_of_finrank_eq_zero
  simp only [Module.finrank_tensorProduct, hE, zero_mul]

/-- The opposite zero-factor orientation has the same actual top minimum. -/
theorem minimalSlope_mixedTensorPair_eq_top_of_right_finrank_eq_zero
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hF : Module.finrank K F = 0) :
    (V.mixedTensorPair W hS hN).minimalSlope hS hN = ⊤ := by
  apply minimalSlope_eq_top_of_finrank_eq_zero
  simp only [Module.finrank_tensorProduct, hF, mul_zero]

end ArakelovGeometry.AdelicVectorBundle

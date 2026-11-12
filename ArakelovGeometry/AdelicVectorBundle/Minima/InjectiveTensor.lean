/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
public import ArakelovGeometry.AdelicVectorBundle.Operator.Height
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
public import ArakelovGeometry.AdelicVectorBundle.Tensor.OperatorBaseChange
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Pair

import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import ArakelovGeometry.AdelicVectorBundle.Slope.Dual
import ArakelovGeometry.AdelicVectorBundle.Slope.DualUpper
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMap
import ArakelovGeometry.AdelicVectorBundle.Tensor.Operator
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# First minima of actual injective tensor bundles

Canonical tensor evaluation and the completed injective/operator identity
make map height minus tensor vector degree. The actual nonzero-map and
dual slope inequalities give source Proposition 4.3.75, including zero factors.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

universe u v w

/-- The canonical evaluation equivalence for the ordinary binary tensor. -/
def tensorPairToHomEquiv (K : Type u) [Field K] (E F : Type w)
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K F] :
    (E ⊗[K] F) ≃ₗ[K] (Module.Dual K E →ₗ[K] F) :=
  (binaryTensorEquiv K (BinaryTensorFactors E F)).symm.trans
    (binaryTensorToHomEquiv K (BinaryTensorFactors E F))

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- The actual injective tensor norm is the operator norm from the first
dual to the second original norm, when the second norm is admissible. -/
theorem injectiveTensorPair_norm_eq_dual_operatorNorm (ξ : NormFamily S E)
    (η : NormFamily S F) [hη : η.IsUltrametric]
    [hN : S.IsArchimedeanNormalized]
    (ω : S.Ω) (z : E ⊗[K] F) :
    (ξ.injectiveTensorPair η).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z) =
      ξ.dual.operatorNorm η ω (tensorPairToHomEquiv K E F z) := by
  rw [injectiveTensorPair_norm_tmul, injectiveTensor_norm_eq_operatorNorm]
  change ξ.dual.operatorNorm
    (η.dual.dual.pullback (Module.Dual.eval K F) (Module.eval_apply_injective K)) ω _ = _
  rw [η.dual_dual_pullback_eq]
  rfl

end NormFamily
namespace AdelicVectorBundle

/-- Actual dual map height is minus the actual injective tensor vector degree;
integrability is produced from the tensor bundle, not assumed of the map. -/
theorem mapHeight_dual_eq_neg_injectiveTensorPair_vectorDegree
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    [hW : W.toNormFamily.IsUltrametric]
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (z : {z : E ⊗[K] F // z ≠ 0}) :
    (V.dualOfMeasurableBase).mapHeight W (tensorPairToHomEquiv K E F z.val) =
      (-(V.injectiveTensorPair W).vectorDegree z : ℝ) := by
  let T := V.injectiveTensorPair W
  let D := V.dualOfMeasurableBase
  let f := tensorPairToHomEquiv K E F z.val
  have hf : f ≠ 0 := fun h => z.property
    ((tensorPairToHomEquiv K E F).map_eq_zero_iff.mp h)
  have he (ω : S.Ω) : D.toNormFamily.localHeight W.toNormFamily ⟨f, hf⟩ ω =
      T.toNormFamily.logNorm z.val ω := by
    dsimp only [NormFamily.localHeight, NormFamily.logNorm]
    exact congrArg Real.log
      (V.toNormFamily.injectiveTensorPair_norm_eq_dual_operatorNorm
        W.toNormFamily ω z.val).symm
  have hi : Integrable (D.toNormFamily.localHeight W.toNormFamily ⟨f, hf⟩) S.v :=
    (T.isDominated.integrable_logNorm T.isMeasurable z.val).congr
      (Filter.Eventually.of_forall fun ω => (he ω).symm)
  rw [D.mapHeight_eq_integral W hf hi, vectorDegree,
    NormFamily.vectorDegree_eq_neg_integral, neg_neg]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall he)

variable [S.IsProper]

/-- Every nonzero tensor is bounded using its actual dual map and the actual
finite slope endpoints of both factors. -/
theorem vectorDegree_injectiveTensorPair_le_maximalSlope_add
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    [hV : V.toNormFamily.IsUltrametric] [hW : W.toNormFamily.IsUltrametric]
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (hE : 0 < Module.finrank K E) (hF : 0 < Module.finrank K F)
    (z : {z : E ⊗[K] F // z ≠ 0}) :
    ((V.injectiveTensorPair W).vectorDegree z : EReal) ≤
      V.maximalSlope + W.maximalSlope := by
  let D := V.dualOfMeasurableBase
  let f := tensorPairToHomEquiv K E F z.val
  have hf : f ≠ 0 := fun h => z.property
    ((tensorPairToHomEquiv K E F).map_eq_zero_iff.mp h)
  have hrD : 0 < Module.finrank K (Module.Dual K E) := by
    rwa [Subspace.dual_finrank_eq]
  obtain ⟨a, ha⟩ := V.exists_maximalSlope_eq_coe hE
  obtain ⟨b, hb⟩ := W.exists_maximalSlope_eq_coe hF
  obtain ⟨c, hc⟩ := D.exists_minimalSlope_eq_coe hrD
  have hl := D.neg_maximalSlope_dual_le_minimalSlope_of_lt_top hrD
    ((D.dualOfMeasurableBase).maximalSlope_lt_top)
  rw [V.maximalSlope_dual_dual_eq_of_isUltrametric, ha, hc,
    ← EReal.coe_neg, EReal.coe_le_coe_iff] at hl
  have hu := D.minimalSlope_le_maximalSlope_add_mapHeight_of_ne_zero W f hf
  rw [hc, hb, V.mapHeight_dual_eq_neg_injectiveTensorPair_vectorDegree W z,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hu
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

omit [S.IsProper] in
/-- A zero left factor has the source's empty tensor threshold domain. -/
theorem maximalLogarithmicMinimum_injectiveTensorPair_eq_bot_of_left_finrank_eq_zero
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (hE : Module.finrank K E = 0) :
    (V.injectiveTensorPair W).maximalLogarithmicMinimum = ⊥ := by
  apply maximalLogarithmicMinimum_eq_bot_of_finrank_eq_zero
  rw [Module.finrank_tensorProduct, hE, zero_mul]

omit [S.IsProper] in
/-- A zero right factor gives the same genuine empty tensor convention. -/
theorem maximalLogarithmicMinimum_injectiveTensorPair_eq_bot_of_right_finrank_eq_zero
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (hF : Module.finrank K F = 0) :
    (V.injectiveTensorPair W).maximalLogarithmicMinimum = ⊥ := by
  apply maximalLogarithmicMinimum_eq_bot_of_finrank_eq_zero
  rw [Module.finrank_tensorProduct, hF, mul_zero]

/-- Source Proposition 4.3.75 on the actual injective binary tensor bundle,
without attainment hypotheses and including either zero factor. -/
theorem maximalLogarithmicMinimum_injectiveTensorPair_le_maximalSlope_add
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    [hV : V.toNormFamily.IsUltrametric] [hW : W.toNormFamily.IsUltrametric]
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.injectiveTensorPair W).maximalLogarithmicMinimum ≤
      V.maximalSlope + W.maximalSlope := by
  by_cases hE : Module.finrank K E = 0
  · rw [V.maximalLogarithmicMinimum_injectiveTensorPair_eq_bot_of_left_finrank_eq_zero
      W hE]
    exact bot_le
  by_cases hF : Module.finrank K F = 0
  · rw [V.maximalLogarithmicMinimum_injectiveTensorPair_eq_bot_of_right_finrank_eq_zero
      W hF]
    exact bot_le
  let T := V.injectiveTensorPair W
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨f, _, hf⟩ := (T.le_finrank_degreeThresholdSpan_iff 1 t).mp ht
  exact (EReal.coe_le_coe_iff.mpr (hf 0)).trans
    (V.vectorDegree_injectiveTensorPair_le_maximalSlope_add W
      (Nat.pos_of_ne_zero hE) (Nat.pos_of_ne_zero hF) (f 0))

end AdelicVectorBundle
end ArakelovGeometry

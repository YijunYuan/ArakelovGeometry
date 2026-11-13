/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Vector
public import ArakelovGeometry.AdelicVectorBundle.Operator.Height
public import ArakelovGeometry.AdelicVectorBundle.Tensor.OperatorBaseChange
public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairOperator

import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import ArakelovGeometry.AdelicVectorBundle.Operator.Comparison
import ArakelovGeometry.AdelicVectorBundle.Tensor.Operator
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Map heights as injective tensor vector degrees

The map is represented by Mathlib's canonical dual-tensor/Hom equivalence.
Both local norms and global degrees use the actual injective tensor family.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type (max u w)} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- The finite tensor evaluation map becomes the standard dual-tensor map
after canonical evaluation of the original vector space. -/
theorem binaryTensorToHom_dual_comp_eval
    (z : ⨂[K] i, BinaryTensorFactors (Module.Dual K E) F i) :
    (binaryTensorToHom K (BinaryTensorFactors (Module.Dual K E) F) z).comp
        (Module.Dual.eval K E) =
      dualTensorHom K E F (binaryTensorEquiv K (BinaryTensorFactors (Module.Dual K E) F) z) := by
  ext x
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a y => simp
  | add z t hz ht => simp_all only [map_add, LinearMap.add_apply, LinearMap.comp_apply]

section IndependentFactors

universe w'

variable {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The nonzero tensor representing a nonzero map under the standard
dual-tensor/Hom equivalence. -/
def linearMapTensor (f : {f : E →ₗ[K] F // f ≠ 0}) :
    {z : Module.Dual K E ⊗[K] F // z ≠ 0} :=
  ⟨(dualTensorHomEquiv K E F).symm f.val, fun h ↦ f.property
    ((dualTensorHomEquiv K E F).symm.map_eq_zero_iff.mp h)⟩

omit [FiniteDimensional K F] in
@[simp]
theorem dualTensorHom_linearMapTensor (f : {f : E →ₗ[K] F // f ≠ 0}) :
    dualTensorHom K E F (linearMapTensor f).val = f.val :=
  (dualTensorHomEquiv K E F).apply_symm_apply f.val

namespace NormFamily

/-- The exact completed injective tensor/Hom identity, with both original
families replaced by their canonical bidual norms. -/
theorem injectiveTensorPair_dual_norm_eq_bidual_operatorNorm (ξ : NormFamily S E)
    (η : NormFamily S F) (ω : S.Ω) (z : Module.Dual K E ⊗[K] F) :
    (ξ.dual.injectiveTensorPair η).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z) =
      (ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)).operatorNorm
        (η.dual.dual.pullback (Module.Dual.eval K F) (Module.eval_apply_injective K))
        ω (dualTensorHom K E F z) := by
  rw [injectiveTensorPair_norm_eq_operatorNorm]
  have h := ξ.dual.dual.operatorNorm_comp_equiv
    (η.dual.dual.pullback (Module.Dual.eval K F) (Module.eval_apply_injective K))
    (Module.evalEquiv K E)
    (tensorPairToHomEquiv K (Module.Dual K E) F z) ω
  simp only [Module.evalEquiv_toLinearMap] at h
  rw [tensorPairToHomEquiv_dual_comp_eval] at h
  exact h.symm

/-- At the source's ultrametric/normalized norms, both biduals are the original
norms, giving the exact operator norm on the ordinary dual tensor product. -/
theorem injectiveTensorPair_dual_norm_eq_operatorNorm (ξ : NormFamily S E)
    (η : NormFamily S F) [hξ : ξ.IsUltrametric] [hη : η.IsUltrametric]
    [hN : S.IsArchimedeanNormalized]
    (ω : S.Ω) (z : Module.Dual K E ⊗[K] F) :
    (ξ.dual.injectiveTensorPair η).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z) =
      ξ.operatorNorm η ω (dualTensorHom K E F z) := by
  rw [injectiveTensorPair_dual_norm_eq_bidual_operatorNorm,
    ξ.dual_dual_pullback_eq, η.dual_dual_pullback_eq]

/-- The local height is the logarithmic norm of the actual representing tensor. -/
theorem localHeight_eq_logNorm_tensor (ξ : NormFamily S E) (η : NormFamily S F)
    [hξ : ξ.IsUltrametric] [hη : η.IsUltrametric]
    [hN : S.IsArchimedeanNormalized]
    (f : {f : E →ₗ[K] F // f ≠ 0}) (ω : S.Ω) :
    ξ.localHeight η f ω = (ξ.dual.injectiveTensorPair η).logNorm (linearMapTensor f).val ω := by
  dsimp only [localHeight, logNorm]
  rw [injectiveTensorPair_dual_norm_eq_operatorNorm ξ η,
    dualTensorHom_linearMapTensor]

end NormFamily

namespace AdelicVectorBundle

/-- Source Definition4.3.17: with ultrametric finite-place norms, map height
is minus the vector degree in the actual injective dual tensor bundle. -/
theorem mapHeight_eq_neg_tensor_vectorDegree (V : AdelicVectorBundle S)
    (W : AdelicVectorBundle S) [hV : V.toNormFamily.IsUltrametric]
    [hW : W.toNormFamily.IsUltrametric]
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (f : {f : V →ₗ[K] W // f ≠ 0}) :
    let T := (V.dualOfMeasurableBase).injectiveTensorPair W
    V.mapHeight W f.val =
      (-(T.toNormFamily.vectorDegree (hd := T.isDominated) (hm := T.isMeasurable)
        (linearMapTensor f)) : ℝ) := by
  intro T
  have he (ω : S.Ω) : V.toNormFamily.localHeight W.toNormFamily f ω =
      T.toNormFamily.logNorm (linearMapTensor f).val ω :=
    V.toNormFamily.localHeight_eq_logNorm_tensor W.toNormFamily f ω
  have hi : Integrable (V.toNormFamily.localHeight W.toNormFamily f) S.v :=
    (T.isDominated.integrable_logNorm T.isMeasurable (linearMapTensor f).val).congr
      (Filter.Eventually.of_forall fun ω ↦ (he ω).symm)
  rw [V.mapHeight_eq_integral W f.property hi, NormFamily.vectorDegree_eq_neg_integral, neg_neg]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall he

end AdelicVectorBundle

end IndependentFactors

end

end ArakelovGeometry

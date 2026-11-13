/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Pair
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Operator
public import ArakelovGeometry.AdelicVectorBundle.Operator.Comparison
import ArakelovGeometry.AdelicVectorBundle.Dual.Map

/-!
# Binary tensor evaluation across universes

The lifted finite tensor model computes the canonical operator on the original
factors. The lifts disappear from both the resulting map and its norm identity.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section
namespace ArakelovGeometry

universe u w w'

variable {K : Type u} [Field K]
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

omit [FiniteDimensional K F] in
/-- Finite lifted evaluation is the original evaluation in the lifted coordinates. -/
theorem tensorPairToHomEquiv_lifted (z : E ⊗[K] F) :
    let e : ULift.{w'} E ≃ₗ[K] E := ULift.moduleEquiv
    let d : ULift.{w} F ≃ₗ[K] F := ULift.moduleEquiv
    binaryTensorToHom K (LiftedTensorFactors E F) ((tensorPairEquiv K E F).symm z) =
      d.symm.toLinearMap.comp
        ((tensorPairToHomEquiv K E F z).comp e.symm.dualMap.toLinearMap) := by
  intro e d
  obtain ⟨t, rfl⟩ := (tensorPairEquiv K E F).surjective z
  rw [LinearEquiv.symm_apply_apply]
  apply LinearMap.ext
  intro φ
  induction t using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    simp [tensorPairEquiv_tprod, LinearEquiv.dualMap_apply, e, d]
  | add t s ht hs =>
    simpa only [map_add, LinearMap.add_apply, LinearMap.comp_apply] using congrArg₂ (· + ·) ht hs

omit [FiniteDimensional K F] in
/-- Evaluation of the first bidual recovers the ordinary dual-tensor map. -/
theorem tensorPairToHomEquiv_dual_comp_eval (z : Module.Dual K E ⊗[K] F) :
    (tensorPairToHomEquiv K (Module.Dual K E) F z).comp (Module.Dual.eval K E) =
      dualTensorHom K E F z := by
  ext x
  induction z using TensorProduct.inductionOn with
  | tmul f y => simp
  | add z t hz ht =>
    simpa only [map_add, LinearMap.add_apply, LinearMap.comp_apply] using congrArg₂ (· + ·) hz ht

namespace NormFamily

variable {S : AdelicStructure K}

/-- The binary injective norm is the operator norm from the first dual to the
second bidual, for independently sized original factors. -/
theorem injectiveTensorPair_norm_eq_operatorNorm (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (z : E ⊗[K] F) :
    (ξ.injectiveTensorPair η).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z) =
      ξ.dual.operatorNorm
        (η.dual.dual.pullback (Module.Dual.eval K F) (Module.eval_apply_injective K))
        ω (tensorPairToHomEquiv K E F z) := by
  let e : ULift.{w'} E ≃ₗ[K] E := ULift.moduleEquiv
  let d : ULift.{w} F ≃ₗ[K] F := ULift.moduleEquiv
  rw [injectiveTensorPair_norm_tmul, injectiveTensor_norm_eq_operatorNorm]
  change (ξ.pullback e.toLinearMap e.injective).dual.operatorNorm
    ((η.pullback d.toLinearMap d.injective).dual.dual.pullback
      (Module.Dual.eval K (ULift.{w} F)) (Module.eval_apply_injective K)) ω
    (binaryTensorToHom K (LiftedTensorFactors E F) ((tensorPairEquiv K E F).symm z)) = _
  rw [ξ.pullbackEquiv_dual e, η.pullbackEquiv_bidual d, tensorPairToHomEquiv_lifted]
  exact ξ.dual.operatorNorm_pullback_equiv _ e.symm.dualMap d
    (tensorPairToHomEquiv K E F z) ω

end NormFamily
end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.TensorGraded
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.AdaptedBasis
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.BidualHN
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Dual
public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairNorm

/-!
# Actual epsilon tensor norms and trivial-place filtrations

The canonical binary injective norm realizes the intrinsic tensor convolution.
Single adapted bases in the two factors suffice.
-/

@[expose] public section

open scoped TensorProduct
open Module

namespace ArakelovGeometry.NormFamily

open AdelicStructure

noncomputable section

universe u v
variable {K : Type u} [Field K] {E V : Type v}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (ξ : NormFamily (singleTrivialPlace K) E) (η : NormFamily (singleTrivialPlace K) V)

/-- The actual binary epsilon norm is ultrametric at the trivial place. -/
theorem injectiveTensorPair_isUltrametric : (ξ.injectiveTensorPair η).IsUltrametric := by
  intro ω hω x y
  change (injectiveTensor (tensorPairFactors ξ η)).norm ω
      ((binaryTensorEquiv K (BinaryTensorFactors E V)).symm.toLinearMap.baseChange _ (x + y)) ≤ _
  rw [map_add]
  exact injectiveTensor_isUltrametric (tensorPairFactors ξ η) ω hω _ _

/-- The actual epsilon norm on rational pure tensors is bounded by the product norm. -/
theorem trivialSeminorm_injectiveTensorPair_tmul_le (x : E) (y : V) :
    (ξ.injectiveTensorPair η).trivialSeminorm (x ⊗ₜ[K] y) ≤
      ξ.trivialSeminorm x * η.trivialSeminorm y := by
  classical
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  rw [trivialSeminorm_apply, trivialSeminorm_apply, trivialSeminorm_apply]
  apply (injectiveTensorPair_norm_le_projectiveTensorPair_norm ξ η PUnit.unit _).trans
  have h := projectiveTensorPair_norm_tmul_completed_le ξ η PUnit.unit
    ((1 : C) ⊗ₜ[K] x) ((1 : C) ⊗ₜ[K] y)
  change (ξ.projectiveTensorPair η).norm PUnit.unit
    ((TensorProduct.AlgebraTensorModule.distribBaseChange K C E V).symm
      (((1 : C) ⊗ₜ[K] x) ⊗ₜ[C] ((1 : C) ⊗ₜ[K] y))) ≤ _ at h
  simpa only [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, one_mul] using h

/-- The canonical dual tensor functional has at most the product of the actual dual norms. -/
theorem trivialSeminorm_injectiveTensorPair_dual_tmul_le
    (ℓ : Module.Dual K E) (m : Module.Dual K V) :
    (ξ.injectiveTensorPair η).dual.trivialSeminorm
      (TensorProduct.dualDistrib K E V (ℓ ⊗ₜ[K] m)) ≤
        ξ.dual.trivialSeminorm ℓ * η.dual.trivialSeminorm m := by
  classical
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  rw [trivialSeminorm_apply, trivialSeminorm_apply, trivialSeminorm_apply]
  have h := injectiveTensorPair_dual_norm_tmul_le ξ η PUnit.unit
    ((1 : C) ⊗ₜ[K] ℓ) ((1 : C) ⊗ₜ[K] m)
  change (ξ.injectiveTensorPair η).dual.norm PUnit.unit
    ((TensorProduct.dualDistrib K E V).baseChange C
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K C (Dual K E) (Dual K V)).symm
        (((1 : C) ⊗ₜ[K] ℓ) ⊗ₜ[C] ((1 : C) ⊗ₜ[K] m)))) ≤ _ at h
  simpa only [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, one_mul,
    LinearMap.baseChange_tmul] using h

end

end ArakelovGeometry.NormFamily

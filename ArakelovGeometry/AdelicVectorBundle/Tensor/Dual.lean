/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Pair
import ArakelovGeometry.AdelicVectorBundle.Tensor.PairNorm
import ArakelovGeometry.Analysis.Determinant.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Actual completed tensor dual functionals

Mathlib's canonical dual tensor map commutes with the existing completed
dual and binary tensor identifications. Injective evaluation gives its
actual operator bound.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

section Algebra

universe wA

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (E F : Type wA) [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The canonical tensor-dual map has the product pairing on arbitrary
actual scalar-extended primal and dual vectors. -/
theorem dualDistrib_baseChange_apply
    (α : L ⊗[K] Module.Dual K E) (β : L ⊗[K] Module.Dual K F)
    (x : L ⊗[K] E) (y : L ⊗[K] F) :
    dualBaseChangeEquiv K L (E ⊗[K] F)
      ((TensorProduct.dualDistrib K E F).baseChange L
        ((TensorProduct.AlgebraTensorModule.distribBaseChange K L
          (Module.Dual K E) (Module.Dual K F)).symm (α ⊗ₜ[L] β)))
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm
        (x ⊗ₜ[L] y)) =
      dualBaseChangeEquiv K L E α x * dualBaseChangeEquiv K L F β y := by
  induction α using TensorProduct.inductionOn with
  | add α₁ α₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add,
      LinearMap.add_apply, h₁, h₂, add_mul]
  | tmul a f =>
    induction β using TensorProduct.inductionOn with
    | add β₁ β₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add,
        LinearMap.add_apply, h₁, h₂, mul_add]
    | tmul b g =>
      induction x using TensorProduct.inductionOn with
      | add x₁ x₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂, add_mul]
      | tmul c e =>
        induction y using TensorProduct.inductionOn with
        | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂, mul_add]
        | tmul d v =>
          simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
            LinearMap.baseChange_tmul, dualBaseChangeEquiv_tmul_apply_tmul,
            TensorProduct.dualDistrib_apply, map_mul]
          ring

end Algebra

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- The canonical tensor of two completed dual vectors is bounded in the
actual dual of the injective binary tensor norm by their dual norm product. -/
theorem injectiveTensorPair_dual_norm_tmul_le
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (α : (S.ϕ ω).Completion ⊗[K] Module.Dual K E)
    (β : (S.ϕ ω).Completion ⊗[K] Module.Dual K F) :
    (ξ.injectiveTensorPair η).dual.norm ω
      ((TensorProduct.dualDistrib K E F).baseChange (S.ϕ ω).Completion
        ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion
          (Module.Dual K E) (Module.Dual K F)).symm
            (α ⊗ₜ[(S.ϕ ω).Completion] β))) ≤
      ξ.dual.norm ω α * η.dual.norm ω β := by
  let L := (S.ϕ ω).Completion
  let X := fun i ↦ L ⊗[K] BinaryTensorFactors E F i
  let : ∀ i, NormedAddCommGroup (X i) :=
    fun i ↦ (tensorPairFactors ξ η i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (tensorPairFactors ξ η i).fibreNormedSpace ω
  let φ : ∀ i, X i →ₗ[L] L := fun i ↦ match i with
    | .inl _ => dualBaseChangeEquiv K L E α
    | .inr _ => dualBaseChangeEquiv K L F β
  let q := (TensorProduct.dualDistrib K E F).baseChange L
    ((TensorProduct.AlgebraTensorModule.distribBaseChange K L
      (Module.Dual K E) (Module.Dual K F)).symm (α ⊗ₜ[L] β))
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L E F
  let B := (binaryTensorEquiv K (BinaryTensorFactors E F)).baseChange K L _ _
  let P := binaryTensorEquiv L X
  have heval : (dualBaseChangeEquiv K L (E ⊗[K] F) q).comp
      (A.symm.toLinearMap.comp P.toLinearMap) = tensorDualEval φ := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change dualBaseChangeEquiv K L (E ⊗[K] F) q
      (A.symm (P (⨂ₜ[L] i, x i))) = tensorDualEval φ (⨂ₜ[L] i, x i)
    simp only [P, binaryTensorEquiv_tprod, A, q, tensorDualEval_tprod, φ,
      Fintype.prod_sum_type, Fintype.prod_unique]
    exact dualDistrib_baseChange_apply K L E F α β (x (.inl ())) (x (.inr ()))
  apply (ξ.injectiveTensorPair η).dual_norm_le ω q
    (mul_nonneg (ξ.dual.norm_nonneg ω α) (η.dual.norm_nonneg ω β))
  intro u
  let v := tensorBaseChangeEquiv K L (BinaryTensorFactors E F) (B.symm u)
  have hP : P v = A u := by
    have h := DFunLike.congr_fun (tensorBaseChangeEquiv_binary K L E F) (B.symm u)
    change P v = A (B (B.symm u)) at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  have he := DFunLike.congr_fun heval v
  change dualBaseChangeEquiv K L (E ⊗[K] F) q (A.symm (P v)) = tensorDualEval φ v at he
  rw [hP, LinearEquiv.symm_apply_apply] at he
  rw [he]
  have hprod : (∏ i, linearMapOperatorSeminorm (φ i)) =
      ξ.dual.norm ω α * η.dual.norm ω β := by
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, φ]
    rfl
  have h := norm_tensorDualEval_le_injective φ v
  rw [hprod] at h
  change ‖tensorDualEval φ v‖ ≤
    (ξ.dual.norm ω α * η.dual.norm ω β) * ArakelovGeometry.injectiveTensorSeminorm v
  simpa only [mul_comm] using h

end NormFamily

end

end ArakelovGeometry

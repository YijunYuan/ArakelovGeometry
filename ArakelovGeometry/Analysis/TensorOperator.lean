/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.ScalarExtensionDual
public import ArakelovGeometry.Analysis.TensorNorm
public import Mathlib.LinearAlgebra.Contraction

/-!
# Injective tensors and operator norms

The binary finite tensor product is identified with the ordinary tensor product.
Its evaluation operator acts from the dual of the first factor to the bidual of
the second. The injective norm is the actual operator norm of this map.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

section Algebra

variable (R : Type*) [CommRing R] (E : Unit ⊕ Unit → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]

/-- The canonical equivalence between a binary finite tensor and a tensor product. -/
def binaryTensorEquiv : (⨂[R] i, E i) ≃ₗ[R] E (.inl ()) ⊗[R] E (.inr ()) :=
  (PiTensorProduct.tmulEquivDep R E).symm.trans
    (TensorProduct.congr (PiTensorProduct.subsingletonEquiv ())
      (PiTensorProduct.subsingletonEquiv ()))

@[simp]
theorem binaryTensorEquiv_tprod (x : ∀ i, E i) :
    binaryTensorEquiv R E (⨂ₜ[R] i, x i) = x (.inl ()) ⊗ₜ[R] x (.inr ()) := by
  simp [binaryTensorEquiv, PiTensorProduct.tmulEquivDep_symm_apply]

/-- The evaluation operator of an actual tensor, using both canonical bidual maps. -/
def binaryTensorOperator : (⨂[R] i, E i) →ₗ[R]
    Module.Dual R (E (.inl ())) →ₗ[R] Module.Dual R (Module.Dual R (E (.inr ()))) :=
  (dualTensorHom R _ _).comp
    ((TensorProduct.map (Module.Dual.eval R (E (.inl ())))
      (Module.Dual.eval R (E (.inr ())))).comp (binaryTensorEquiv R E).toLinearMap)

@[simp]
theorem binaryTensorOperator_tprod (x : ∀ i, E i)
    (f : Module.Dual R (E (.inl ()))) (g : Module.Dual R (E (.inr ()))) :
    binaryTensorOperator R E (⨂ₜ[R] i, x i) f g = f (x (.inl ())) * g (x (.inr ())) := by
  simp [binaryTensorOperator]

/-- Product dual evaluation agrees with the canonical evaluation operator. -/
theorem dualDistrib_eq_binaryTensorOperator (z : ⨂[R] i, E i)
    (φ : ∀ i, Module.Dual R (E i)) :
    PiTensorProduct.dualDistrib (⨂ₜ[R] i, φ i) z =
      binaryTensorOperator R E z (φ (.inl ())) (φ (.inr ())) := by
  have h : PiTensorProduct.dualDistrib (⨂ₜ[R] i, φ i) =
      ((LinearMap.applyₗ (φ (.inr ()))).comp
        ((LinearMap.applyₗ (φ (.inl ()))).comp (binaryTensorOperator R E))) := by
    apply PiTensorProduct.ext
    ext x
    simp [PiTensorProduct.dualDistrib_apply, Fintype.prod_sum_type]
  exact LinearMap.congr_fun h z

end Algebra

section Norm

variable {L : Type*} [NormedField L] [CompleteSpace L]
  {E : Unit ⊕ Unit → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace L (E i)] [∀ i, FiniteDimensional L (E i)]

/-- The injective norm is the operator norm from the first dual to the second
bidual, with the actual operator norms on both algebraic duals. -/
theorem injectiveTensorSeminorm_eq_binaryTensorOperator (z : ⨂[L] i, E i) :
    let := linearDualNormedAddCommGroup (k := L) (E := E (.inl ()))
    let := linearDualNormedSpace (k := L) (E := E (.inl ()))
    let := linearDualNormedAddCommGroup (k := L) (E := E (.inr ()))
    let := linearDualNormedSpace (k := L) (E := E (.inr ()))
    let := linearDualNormedAddCommGroup (k := L) (E := Module.Dual L (E (.inr ())))
    let := linearDualNormedSpace (k := L) (E := Module.Dual L (E (.inr ())))
    injectiveTensorSeminorm z = linearMapOperatorSeminorm (binaryTensorOperator L E z) := by
  intro leftGroup leftSpace rightGroup rightSpace bidualGroup bidualSpace
  let := leftGroup
  let := leftSpace
  let := rightGroup
  let := rightSpace
  let := bidualGroup
  let := bidualSpace
  have hprod (φ : ∀ i, Module.Dual L (E i)) :
      (∏ i, linearMapOperatorSeminorm (φ i)) = ‖φ (.inl ())‖ * ‖φ (.inr ())‖ := by
    simp only [Fintype.prod_sum_type, Fintype.prod_unique]
    rfl
  have heval (φ : ∀ i, Module.Dual L (E i)) :
      tensorDualEval φ z = binaryTensorOperator L E z (φ (.inl ())) (φ (.inr ())) :=
    dualDistrib_eq_binaryTensorOperator L E z φ
  apply le_antisymm
  · apply (injectiveTensorSeminorm_le_iff z _).mpr
    intro φ
    rw [heval, hprod]
    by_cases hd : ‖φ (.inl ())‖ * ‖φ (.inr ())‖ = 0
    · rw [hd, div_zero]
      exact apply_nonneg _ _
    apply (div_le_iff₀ (lt_of_le_of_ne
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Ne.symm hd))).mpr
    calc
      ‖binaryTensorOperator L E z (φ (.inl ())) (φ (.inr ()))‖
          ≤ ‖binaryTensorOperator L E z (φ (.inl ()))‖ * ‖φ (.inr ())‖ :=
        norm_linearMap_apply_le _ _
      _ ≤ (linearMapOperatorSeminorm (binaryTensorOperator L E z) *
          ‖φ (.inl ())‖) * ‖φ (.inr ())‖ :=
        mul_le_mul_of_nonneg_right (norm_linearMap_apply_le _ _) (norm_nonneg _)
      _ = _ := mul_assoc _ _ _
  · apply linearMapOperatorSeminorm_le _ (apply_nonneg _ _)
    intro f
    change linearMapOperatorSeminorm (binaryTensorOperator L E z f) ≤ _
    apply linearMapOperatorSeminorm_le _ (mul_nonneg (apply_nonneg _ _) (norm_nonneg _))
    intro g
    by_cases hf : f = 0
    · simp [hf]
    by_cases hg : g = 0
    · simp [hg]
    let φ : ∀ i, Module.Dual L (E i) := Sum.rec (fun _ ↦ f) (fun _ ↦ g)
    have h := tensorDualRatioSeminorm_le_injective φ z
    rw [tensorDualRatioSeminorm_apply, heval, hprod] at h
    have h' := (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hf) (norm_pos_iff.mpr hg))).mp h
    simpa only [mul_assoc] using h'

end Norm

end

end ArakelovGeometry

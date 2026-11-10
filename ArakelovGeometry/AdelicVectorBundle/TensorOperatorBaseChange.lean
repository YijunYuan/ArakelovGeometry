/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.TensorBaseChange
public import ArakelovGeometry.Analysis.TensorOperator

/-!
# Tensor evaluation operators and scalar extension

These maps use the canonical algebraic dual and the existing tensor base-change
equivalence. No choice of coordinates enters the resulting operator.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable (K : Type*) [Field K] (E : Unit ⊕ Unit → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

/-- A tensor gives a map from the dual of its first factor to its second factor. -/
def binaryTensorToHom : (⨂[K] i, E i) →ₗ[K]
    Module.Dual K (E (.inl ())) →ₗ[K] E (.inr ()) :=
  (dualTensorHom K _ _).comp
    ((TensorProduct.map (Module.Dual.eval K (E (.inl ())))
      (LinearMap.id : E (.inr ()) →ₗ[K] E (.inr ()))).comp
        (binaryTensorEquiv K E).toLinearMap)

@[simp]
theorem binaryTensorToHom_tprod (x : ∀ i, E i) (f : Module.Dual K (E (.inl ()))) :
    binaryTensorToHom K E (⨂ₜ[K] i, x i) f = f (x (.inl ())) • x (.inr ()) := by
  simp [binaryTensorToHom]

/-- The canonical tensor operator is evaluation of the tensor-to-Hom map. -/
theorem binaryTensorOperator_eq_eval (z : ⨂[K] i, E i) :
    binaryTensorOperator K E z =
      (Module.Dual.eval K (E (.inr ()))).comp (binaryTensorToHom K E z) := by
  have h : binaryTensorOperator K E =
      (LinearMap.compRight K (Module.Dual.eval K (E (.inr ())))).comp
        (binaryTensorToHom K E) := by
    apply PiTensorProduct.ext
    ext x f g
    simp
  exact LinearMap.congr_fun h z

variable [∀ i, FiniteDimensional K (E i)]

/-- The tensor-to-Hom identification is an equivalence in finite dimension. -/
def binaryTensorToHomEquiv : (⨂[K] i, E i) ≃ₗ[K]
    Module.Dual K (E (.inl ())) →ₗ[K] E (.inr ()) :=
  (binaryTensorEquiv K E).trans
    ((TensorProduct.congr (Module.evalEquiv K (E (.inl ()))) (LinearEquiv.refl K _)).trans
      (dualTensorHomEquiv K _ _))

@[simp]
theorem binaryTensorToHomEquiv_apply (z : ⨂[K] i, E i) :
    binaryTensorToHomEquiv K E z = binaryTensorToHom K E z := rfl

variable (L : Type*) [Field L] [Algebra K L]

/-- Rational tensor evaluation commutes with actual scalar extension of maps. -/
theorem binaryTensorToHom_baseChange (z : ⨂[K] i, E i)
    (f : L ⊗[K] Module.Dual K (E (.inl ()))) :
    binaryTensorToHom L (fun i ↦ L ⊗[K] E i)
        (tensorBaseChangeEquiv K L E ((1 : L) ⊗ₜ[K] z))
        (dualBaseChangeEquiv K L (E (.inl ())) f) =
      (binaryTensorToHom K E z).baseChange L f := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
      induction f using TensorProduct.inductionOn with
      | add f g hf hg => simp_all only [map_add]
      | tmul b φ =>
          simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
            Algebra.smul_def, mul_left_comm, mul_comm]
  | add z t hz ht =>
      simp_all only [TensorProduct.tmul_add, map_add, LinearMap.add_apply,
        LinearMap.baseChange_add]

end

end ArakelovGeometry

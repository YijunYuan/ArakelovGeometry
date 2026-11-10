/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Scalar extension of finite tensor products

The canonical scalar-extension equivalence for finite tensor products of
vector spaces, including the empty tensor product.
-/

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable {ι : Type*}
variable (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

/-- The canonical scalar-extension map for a finite tensor product. -/
def tensorBaseChange :
    (L ⊗[K] (⨂[K] i, E i)) →ₗ[L] (⨂[L] i, L ⊗[K] E i) :=
  LinearMap.liftBaseChange L (PiTensorProduct.lift
    (((PiTensorProduct.tprod L).restrictScalars K).compLinearMap
      (fun i ↦ TensorProduct.mk K L (E i) 1)))

/-- The canonical map on a scalar multiple of a pure tensor. -/
@[simp]
theorem tensorBaseChange_tmul_tprod (a : L) (x : ∀ i, E i) :
    tensorBaseChange K L E (a ⊗ₜ[K] (⨂ₜ[K] i, x i)) =
      a • (⨂ₜ[L] i, (1 : L) ⊗ₜ[K] x i) := by
  simp [tensorBaseChange]

variable [Finite ι]

/-- Any choice of factor bases identifies the canonical map with the induced
basis equivalence. Thus the canonical map does not depend on such a choice. -/
theorem tensorBaseChange_eq_basisEquiv {κ : ι → Type*}
    (b : ∀ i, Module.Basis (κ i) K (E i)) :
    tensorBaseChange K L E =
      (((Basis.piTensorProduct b).baseChange L).equiv
        (Basis.piTensorProduct (fun i ↦ (b i).baseChange L)) (Equiv.refl _)).toLinearMap := by
  apply ((Basis.piTensorProduct b).baseChange L).ext
  intro j
  rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
  simp [Module.Basis.baseChange_apply, Basis.piTensorProduct_apply]

/-- Finite tensor products commute with scalar extension, including empty families. -/
theorem tensorBaseChange_bijective : Function.Bijective (tensorBaseChange K L E) := by
  rw [tensorBaseChange_eq_basisEquiv K L E (fun i ↦ Module.Free.chooseBasis K (E i))]
  exact LinearEquiv.bijective _

/-- The canonical equivalence between the scalar extension of a finite tensor
product and the tensor product of the scalar extensions. -/
def tensorBaseChangeEquiv :
    (L ⊗[K] (⨂[K] i, E i)) ≃ₗ[L] (⨂[L] i, L ⊗[K] E i) :=
  LinearEquiv.ofBijective (tensorBaseChange K L E) (tensorBaseChange_bijective K L E)

@[simp]
theorem tensorBaseChangeEquiv_apply (z : L ⊗[K] (⨂[K] i, E i)) :
    tensorBaseChangeEquiv K L E z = tensorBaseChange K L E z := rfl

@[simp]
theorem tensorBaseChangeEquiv_tmul_tprod (a : L) (x : ∀ i, E i) :
    tensorBaseChangeEquiv K L E (a ⊗ₜ[K] (⨂ₜ[K] i, x i)) =
      a • (⨂ₜ[L] i, (1 : L) ⊗ₜ[K] x i) :=
  tensorBaseChange_tmul_tprod K L E a x

/-- The inverse equivalence multiplies the scalar coordinates of a pure
tensor, with the empty product equal to one. -/
@[simp]
theorem tensorBaseChangeEquiv_symm_tprod_tmul [Fintype ι]
    (a : ι → L) (x : ∀ i, E i) :
    (tensorBaseChangeEquiv K L E).symm (⨂ₜ[L] i, a i ⊗ₜ[K] x i) =
      (∏ i, a i) ⊗ₜ[K] (⨂ₜ[K] i, x i) := by
  apply (tensorBaseChangeEquiv K L E).injective
  rw [LinearEquiv.apply_symm_apply, tensorBaseChangeEquiv_tmul_tprod]
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
    (PiTensorProduct.tprod L).map_smul_univ a (fun i ↦ (1 : L) ⊗ₜ[K] x i)

end

end ArakelovGeometry

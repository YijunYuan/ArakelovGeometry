/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.BaseChange
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Scalar extension of exterior powers

Canonical exterior scalar extension, including degree zero, and compatibility
with the canonical quotient of the corresponding tensor power.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable (K L E : Type*) [Field K] [Field L] [Algebra K L]
  [AddCommGroup E] [Module K E] (n : ℕ)

/-- The canonical map from the scalar extension of an exterior power to the
exterior power of the scalar extension. -/
def exteriorBaseChange : (L ⊗[K] (⋀[K]^n E)) →ₗ[L] (⋀[L]^n (L ⊗[K] E)) :=
  LinearMap.liftBaseChange L (exteriorPower.alternatingMapLinearEquiv {
    toMultilinearMap :=
      (((exteriorPower.ιMulti L n).toMultilinearMap).restrictScalars K).compLinearMap
        (fun _ ↦ TensorProduct.mk K L E 1)
    map_eq_zero_of_eq' := fun x _ _ h hij ↦
      (exteriorPower.ιMulti L n).map_eq_zero_of_eq (fun k ↦ (1 : L) ⊗ₜ[K] x k)
        (congrArg (fun e ↦ (1 : L) ⊗ₜ[K] e) h) hij })

/-- The defining scalar-extension formula on decomposable exterior tensors. -/
@[simp]
theorem exteriorBaseChange_tmul_ιMulti (a : L) (x : Fin n → E) :
    exteriorBaseChange K L E n (a ⊗ₜ[K] exteriorPower.ιMulti K n x) =
      a • exteriorPower.ιMulti L n (fun i ↦ (1 : L) ⊗ₜ[K] x i) := by
  simp [exteriorBaseChange]
  rfl

/-- An arbitrary ordered factor basis exhibits the canonical map as a basis
equivalence; the map itself is independent of this choice. -/
theorem exteriorBaseChange_eq_basisEquiv {κ : Type*} [LinearOrder κ]
    (b : Module.Basis κ K E) :
    exteriorBaseChange K L E n =
      (((b.exteriorPower n).baseChange L).equiv ((b.baseChange L).exteriorPower n)
        (Equiv.refl _)).toLinearMap := by
  apply ((b.exteriorPower n).baseChange L).ext
  intro j
  rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
  simp [Module.Basis.baseChange_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, Function.comp_def]

/-- Exterior powers commute with scalar extension in every degree. -/
theorem exteriorBaseChange_bijective : Function.Bijective (exteriorBaseChange K L E n) := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex K E) := linearOrderOfSTO WellOrderingRel
  rw [exteriorBaseChange_eq_basisEquiv K L E n (Module.Free.chooseBasis K E)]
  exact LinearEquiv.bijective _

/-- The canonical scalar-extension equivalence for exterior powers, including
degree zero and exterior powers above the dimension. -/
def exteriorBaseChangeEquiv : (L ⊗[K] (⋀[K]^n E)) ≃ₗ[L] (⋀[L]^n (L ⊗[K] E)) :=
  LinearEquiv.ofBijective (exteriorBaseChange K L E n)
    (exteriorBaseChange_bijective K L E n)

@[simp]
theorem exteriorBaseChangeEquiv_apply (z : L ⊗[K] (⋀[K]^n E)) :
    exteriorBaseChangeEquiv K L E n z = exteriorBaseChange K L E n z := rfl

@[simp]
theorem exteriorBaseChangeEquiv_tmul_ιMulti (a : L) (x : Fin n → E) :
    exteriorBaseChangeEquiv K L E n (a ⊗ₜ[K] exteriorPower.ιMulti K n x) =
      a • exteriorPower.ιMulti L n (fun i ↦ (1 : L) ⊗ₜ[K] x i) :=
  exteriorBaseChange_tmul_ιMulti K L E n a x

/-- The inverse map on a wedge of scalar-extended pure tensors multiplies
their scalar coordinates. This also includes degree zero. -/
@[simp]
theorem exteriorBaseChangeEquiv_symm_ιMulti_tmul (a : Fin n → L) (x : Fin n → E) :
    (exteriorBaseChangeEquiv K L E n).symm
        (exteriorPower.ιMulti L n (fun i ↦ a i ⊗ₜ[K] x i)) =
      (∏ i, a i) ⊗ₜ[K] exteriorPower.ιMulti K n x := by
  apply (exteriorBaseChangeEquiv K L E n).injective
  rw [LinearEquiv.apply_symm_apply, exteriorBaseChangeEquiv_tmul_ιMulti]
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
    (exteriorPower.ιMulti L n).map_smul_univ a (fun i ↦ (1 : L) ⊗ₜ[K] x i)

/-- The canonical quotient from a tensor power to the exterior power. -/
def tensorToExterior : (⨂[K] (_ : Fin n), E) →ₗ[K] (⋀[K]^n E) :=
  PiTensorProduct.lift (exteriorPower.ιMulti K n).toMultilinearMap

@[simp]
theorem tensorToExterior_tprod (x : Fin n → E) :
    tensorToExterior K E n (⨂ₜ[K] i, x i) = exteriorPower.ιMulti K n x :=
  PiTensorProduct.lift.tprod x

/-- The canonical tensor-to-exterior map is surjective in every degree. -/
theorem tensorToExterior_surjective : Function.Surjective (tensorToExterior K E n) := by
  apply LinearMap.range_eq_top.mp
  apply top_le_iff.mp
  rw [← exteriorPower.ιMulti_span K n E]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  exact ⟨(⨂ₜ[K] i, x i), tensorToExterior_tprod K E n x⟩

/-- In degree zero the canonical quotient is the identity between the two
canonical presentations of the scalar field. -/
theorem tensorToExterior_zero : tensorToExterior K E 0 =
    ((PiTensorProduct.isEmptyEquiv (Fin 0)).trans
      (_root_.exteriorPower.zeroEquiv K E).symm).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  apply (_root_.exteriorPower.zeroEquiv K E).injective
  simp

/-- The degree-zero tensor-to-exterior map is bijective. -/
theorem tensorToExterior_zero_bijective : Function.Bijective (tensorToExterior K E 0) := by
  rw [tensorToExterior_zero]
  exact LinearEquiv.bijective _

/-- Completed tensor and exterior scalar extension commute with the quotient
map from tensor powers to exterior powers. -/
theorem exteriorBaseChangeEquiv_tensorToExterior
    (z : L ⊗[K] (⨂[K] (_ : Fin n), E)) :
    exteriorBaseChangeEquiv K L E n ((tensorToExterior K E n).baseChange L z) =
      tensorToExterior L (L ⊗[K] E) n (tensorBaseChangeEquiv K L (fun _ : Fin n ↦ E) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      simp only [LinearMap.baseChange_tmul, map_smul, tensorToExterior_tprod,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        exteriorBaseChangeEquiv_tmul_ιMulti, tensorBaseChangeEquiv_tmul_tprod]
    | add z t hz ht => simp only [TensorProduct.tmul_add, map_add, hz, ht]
  | add z t hz ht => simp only [map_add, hz, ht]

/-- In degree zero, scalar extension is the usual multiplication map on
the scalar field under the canonical exterior-unit identifications. -/
theorem exteriorBaseChangeEquiv_zero_tmul (a : L) (z : ⋀[K]^0 E) :
    exteriorPower.zeroEquiv L (L ⊗[K] E)
        (exteriorBaseChangeEquiv K L E 0 (a ⊗ₜ[K] z)) =
      a * algebraMap K L (exteriorPower.zeroEquiv K E z) := by
  obtain ⟨r, rfl⟩ := (exteriorPower.zeroEquiv K E).symm.surjective z
  simp only [LinearEquiv.apply_symm_apply]
  rw [exteriorPower.zeroEquiv_symm_apply, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', exteriorBaseChangeEquiv_tmul_ιMulti,
    map_smul, exteriorPower.zeroEquiv_ιMulti]
  simp [Algebra.smul_def, mul_comm]

end

end ArakelovGeometry

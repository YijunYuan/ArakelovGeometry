/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.Determinant.ExactSequence
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite -- shake: keep

/-!
# The algebraic determinant of a tensor product

Tensor-basis determinants obey the Kronecker determinant identity, including
empty factors. This supplies basis independence for the canonical tensor
determinant map on actual exterior powers and powered determinant lines.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable {K : Type*} [Field K]
  {E : Type*} [AddCommGroup E] [Module K E]
  {F : Type*} [AddCommGroup F] [Module K F]
  {n m : ℕ}

/-- The determinant in a tensor basis is the product of the two determinant
coordinates with their rank powers. The tuples need not be bases. -/
theorem tensorProduct_det (b : Module.Basis (Fin n) K E)
    (c : Module.Basis (Fin m) K F) (x : Fin n → E) (y : Fin m → F) :
    (b.tensorProduct c).det (fun ij ↦ x ij.1 ⊗ₜ[K] y ij.2) =
      b.det x ^ m * c.det y ^ n := by
  have hM : (b.tensorProduct c).toMatrix (fun ij ↦ x ij.1 ⊗ₜ[K] y ij.2) =
      Matrix.kroneckerMap (· * ·) (b.toMatrix x) (c.toMatrix y) := by
    ext ⟨i, j⟩ ⟨i', j'⟩
    simp only [Module.Basis.toMatrix_apply,
      Module.Basis.tensorProduct_repr_tmul_apply, Matrix.kroneckerMap_apply,
      smul_eq_mul, mul_comm]
  rw [Module.Basis.det_apply, hM, Matrix.det_kronecker,
    ← Module.Basis.det_apply, ← Module.Basis.det_apply]
  simp only [Fintype.card_fin]

variable [FiniteDimensional K E] [FiniteDimensional K F]

/-- Scalar coordinate on a tensor power of the actual determinant line. -/
def determinantPowerCoordinateEquiv (b : Module.Basis (Fin n) K E) (r : ℕ) :
    (⨂[K] (_ : Fin r), ⋀[K]^n E) ≃ₗ[K] K :=
  (PiTensorProduct.congr (fun _ : Fin r ↦ determinantCoordinateEquiv b)).trans
    (PiTensorProduct.constantBaseRingEquiv (Fin r) K).toLinearEquiv

/-- Powered coordinates multiply the actual determinant coordinates. -/
theorem determinantPowerCoordinateEquiv_tprod
    (b : Module.Basis (Fin n) K E) (r : ℕ) (z : Fin r → ⋀[K]^n E) :
    determinantPowerCoordinateEquiv b r (⨂ₜ[K] i, z i) =
      ∏ i, determinantCoordinateEquiv b (z i) := by
  simp only [determinantPowerCoordinateEquiv, LinearEquiv.trans_apply,
    PiTensorProduct.congr_tprod, AlgEquiv.toLinearEquiv_apply,
    PiTensorProduct.constantBaseRingEquiv_tprod]

/-- The inverse powered coordinate is a scalar multiple of the repeated
basis wedge, including the tensor unit for power zero. -/
theorem determinantPowerCoordinateEquiv_symm
    (b : Module.Basis (Fin n) K E) (r : ℕ) (a : K) :
    (determinantPowerCoordinateEquiv b r).symm a =
      a • (⨂ₜ[K] (_ : Fin r), exteriorPower.ιMulti K n b) := by
  apply (determinantPowerCoordinateEquiv b r).injective
  rw [LinearEquiv.apply_symm_apply, map_smul,
    determinantPowerCoordinateEquiv_tprod]
  simp only [determinantCoordinateEquiv_ιMulti, Module.Basis.det_self,
    Finset.prod_const_one, smul_eq_mul, mul_one]

/-- The determinant tensor map constructed in arbitrary basis coordinates. -/
def determinantTensorEquivOfBases (b : Module.Basis (Fin n) K E)
    (c : Module.Basis (Fin m) K F) :
    ((⨂[K] (_ : Fin m), ⋀[K]^n E) ⊗[K]
      (⨂[K] (_ : Fin n), ⋀[K]^m F)) ≃ₗ[K] (⋀[K]^(n * m) (E ⊗[K] F)) :=
  ((TensorProduct.congr (determinantPowerCoordinateEquiv b m)
    (determinantPowerCoordinateEquiv c n)).trans (TensorProduct.lid K K)).trans
      (determinantCoordinateEquiv
        ((b.tensorProduct c).reindex finProdFinEquiv)).symm

/-- The basis-coordinate map takes powered wedge vectors to the ordered
tensor wedge for arbitrary tuples, including singular and empty ones. -/
theorem determinantTensorEquivOfBases_ιMulti
    (b : Module.Basis (Fin n) K E) (c : Module.Basis (Fin m) K F)
    (x : Fin n → E) (y : Fin m → F) :
    determinantTensorEquivOfBases b c
      ((⨂ₜ[K] (_ : Fin m), exteriorPower.ιMulti K n x) ⊗ₜ[K]
        (⨂ₜ[K] (_ : Fin n), exteriorPower.ιMulti K m y)) =
      exteriorPower.ιMulti K (n * m)
        (fun i ↦ x (finProdFinEquiv.symm i).1 ⊗ₜ[K]
          y (finProdFinEquiv.symm i).2) := by
  apply (determinantCoordinateEquiv
    ((b.tensorProduct c).reindex finProdFinEquiv)).injective
  simp only [determinantTensorEquivOfBases, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, TensorProduct.lid_tmul,
    LinearEquiv.apply_symm_apply, determinantPowerCoordinateEquiv_tprod,
    determinantCoordinateEquiv_ιMulti, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Module.Basis.det_reindex,
    Function.comp_def, Equiv.symm_apply_apply]
  exact (tensorProduct_det b c x y).symm

/-- The actual determinant tensor map is independent of both basis choices. -/
theorem determinantTensorEquivOfBases_eq
    (b b' : Module.Basis (Fin n) K E) (c c' : Module.Basis (Fin m) K F) :
    determinantTensorEquivOfBases b c = determinantTensorEquivOfBases b' c' := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro t
  have hz : z = determinantPowerCoordinateEquiv b m z •
      (⨂ₜ[K] (_ : Fin m), exteriorPower.ιMulti K n b) := by
    rw [← determinantPowerCoordinateEquiv_symm, LinearEquiv.symm_apply_apply]
  have ht : t = determinantPowerCoordinateEquiv c n t •
      (⨂ₜ[K] (_ : Fin n), exteriorPower.ιMulti K m c) := by
    rw [← determinantPowerCoordinateEquiv_symm, LinearEquiv.symm_apply_apply]
  change determinantTensorEquivOfBases b c (z ⊗ₜ[K] t) =
    determinantTensorEquivOfBases b' c' (z ⊗ₜ[K] t)
  rw [hz, ht]
  simp only [TensorProduct.smul_tmul_smul, map_smul,
    determinantTensorEquivOfBases_ιMulti]

end

end ArakelovGeometry

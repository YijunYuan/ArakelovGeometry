/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.ComplexPolarization
public import ArakelovGeometry.Analysis.ScalarExtensionNorm
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hermitian scalar extension

The actual tensor scalar extension carries the positive definite sesquilinear
extension of the original inner product. Its defining pairing identity fixes
the extension independently of an orthonormal basis.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

variable {k L : Type*} [RCLike k] [RCLike L] [NormedAlgebra k L]

/-- An isometric extension of real or complex normed fields commutes with
conjugation, in either complex orientation. -/
theorem normedAlgebra_map_conj (x : k) :
    algebraMap k L (starRingEnd k x) = starRingEnd L (algebraMap k L x) := by
  let σ := rclikeComplexEmbedding L
  have hσ : ∀ y, ‖σ y‖ = ‖y‖ := norm_rclikeComplexEmbedding
  have hτ : ∀ y, ‖(σ.comp (algebraMap k L)) y‖ = ‖y‖ := by
    intro y
    rw [RingHom.comp_apply, hσ, norm_algebraMap']
  apply σ.injective
  exact (complexEmbedding_map_conj (σ.comp (algebraMap k L)) hτ x).trans
    (complexEmbedding_map_conj σ hσ (algebraMap k L x)).symm

/-- An isometric extension of real or complex normed fields fixes the
canonical real scalars. -/
theorem normedAlgebra_map_ofReal (r : ℝ) :
    algebraMap k L (algebraMap ℝ k r) = algebraMap ℝ L r := by
  let σ := rclikeComplexEmbedding L
  have hσ : ∀ y, ‖σ y‖ = ‖y‖ := norm_rclikeComplexEmbedding
  have hτ : ∀ y, ‖(σ.comp (algebraMap k L)) y‖ = ‖y‖ := by
    intro y
    rw [RingHom.comp_apply, hσ, norm_algebraMap']
  apply σ.injective
  exact (complexEmbedding_apply_ofReal (σ.comp (algebraMap k L)) hτ r).trans
    (complexEmbedding_apply_ofReal σ hσ r).symm

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace k E] [Fintype ι]
  (b : OrthonormalBasis ι k E)

/-- Coordinates in the scalar extension of an orthonormal basis, on the
actual tensor scalar extension. -/
def hermitianScalarExtensionCoordinates : (L ⊗[k] E) ≃ₗ[L] EuclideanSpace L ι :=
  (b.toBasis.baseChange L).equivFun.trans (WithLp.linearEquiv 2 L (ι → L)).symm

/-- Pure-tensor coordinates are the scalar extensions of the original
orthonormal coordinates. -/
theorem hermitianScalarExtensionCoordinates_tmul (a : L) (x : E) (i : ι) :
    hermitianScalarExtensionCoordinates (L := L) b (a ⊗ₜ[k] x) i =
      a * algebraMap k L (b.repr x i) := by
  change (b.toBasis.baseChange L).equivFun (a ⊗ₜ[k] x) i = _
  simp only [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
    OrthonormalBasis.coe_toBasis_repr_apply, Algebra.smul_def, mul_comm]

/-- The Hermitian scalar-extension seminorm uses the Euclidean norm of the
extended orthonormal coordinates. -/
def hermitianScalarExtensionSeminorm : Seminorm L (L ⊗[k] E) :=
  (normSeminorm L (EuclideanSpace L ι)).comp
    (hermitianScalarExtensionCoordinates b).toLinearMap

/-- Positive definiteness includes the empty orthonormal basis. -/
theorem hermitianScalarExtensionSeminorm_eq_zero_iff (z : L ⊗[k] E) :
    hermitianScalarExtensionSeminorm b z = 0 ↔ z = 0 := by
  change ‖hermitianScalarExtensionCoordinates b z‖ = 0 ↔ _
  rw [norm_eq_zero, LinearEquiv.map_eq_zero_iff]

/-- The positive definite sesquilinear core on the existing scalar
extension module. -/
@[instance_reducible]
def hermitianScalarExtensionCore : InnerProductSpace.Core L (L ⊗[k] E) where
  inner x y := inner L (hermitianScalarExtensionCoordinates b x)
    (hermitianScalarExtensionCoordinates b y)
  conj_inner_symm _ _ := inner_conj_symm _ _
  re_inner_nonneg _ := inner_self_nonneg
  add_left x y z := by simp only [map_add, inner_add_left]
  smul_left x y a := by simp only [map_smul, inner_smul_left]
  definite x h := (hermitianScalarExtensionCoordinates b).map_eq_zero_iff.mp
    (inner_self_eq_zero.mp h)

/-- The scalar-extension seminorm is exactly the norm of the extended
inner-product core. -/
theorem hermitianScalarExtensionSeminorm_sq (z : L ⊗[k] E) :
    (hermitianScalarExtensionSeminorm b z) ^ 2 =
      RCLike.re ((hermitianScalarExtensionCore b).inner z z) :=
  norm_sq_eq_re_inner (𝕜 := L) (hermitianScalarExtensionCoordinates b z)

/-- Exact extension of the sesquilinear pairing on pure tensors. The
first variable is conjugate-linear, as in Mathlib's inner-product convention. -/
theorem hermitianScalarExtensionCore_tmul (a c : L) (x y : E) :
    (hermitianScalarExtensionCore b).inner (a ⊗ₜ[k] x) (c ⊗ₜ[k] y) =
      starRingEnd L a * c * algebraMap k L (inner k x y) := by
  change inner L (hermitianScalarExtensionCoordinates (L := L) b (a ⊗ₜ[k] x))
    (hermitianScalarExtensionCoordinates (L := L) b (c ⊗ₜ[k] y)) = _
  rw [PiLp.inner_apply, ← b.repr.inner_map_map x y, PiLp.inner_apply]
  simp only [hermitianScalarExtensionCoordinates_tmul, RCLike.inner_apply,
    map_sum, map_mul, normedAlgebra_map_conj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The Hermitian extension restricts to the original norm and scales
exactly on every pure scalar tensor. -/
theorem hermitianScalarExtensionSeminorm_tmul (a : L) (x : E) :
    hermitianScalarExtensionSeminorm b (a ⊗ₜ[k] x) = ‖a‖ * ‖x‖ := by
  apply (sq_eq_sq₀ (apply_nonneg _ _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [hermitianScalarExtensionSeminorm_sq, hermitianScalarExtensionCore_tmul,
    RCLike.conj_mul, inner_self_eq_norm_sq_to_K, map_pow,
    normedAlgebra_map_ofReal]
  simp only [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re, mul_pow]

/-- The exact pairing extension is independent of the orthonormal basis,
since pure tensors span both variables. -/
theorem hermitianScalarExtensionCore_inner_eq {κ : Type*} [Fintype κ]
    (c : OrthonormalBasis κ k E) (z t : L ⊗[k] E) :
    (hermitianScalarExtensionCore b).inner z t =
      (hermitianScalarExtensionCore c).inner z t := by
  change inner L (hermitianScalarExtensionCoordinates b z)
      (hermitianScalarExtensionCoordinates b t) =
    inner L (hermitianScalarExtensionCoordinates c z)
      (hermitianScalarExtensionCoordinates c t)
  induction z using TensorProduct.inductionOn with
  | add z u hz hu => simp only [map_add, inner_add_left, hz, hu]
  | tmul a x =>
    induction t using TensorProduct.inductionOn with
    | add t u ht hu => simp only [map_add, inner_add_right, ht, hu]
    | tmul d y =>
      exact (hermitianScalarExtensionCore_tmul b a d x y).trans
        (hermitianScalarExtensionCore_tmul c a d x y).symm

/-- Consequently the Hermitian scalar-extension norm is independent of
the orthonormal basis, including dimension zero. -/
theorem hermitianScalarExtensionSeminorm_eq {κ : Type*} [Fintype κ]
    (c : OrthonormalBasis κ k E) :
    hermitianScalarExtensionSeminorm (L := L) b = hermitianScalarExtensionSeminorm c := by
  ext z
  apply (sq_eq_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [hermitianScalarExtensionSeminorm_sq, hermitianScalarExtensionSeminorm_sq,
    hermitianScalarExtensionCore_inner_eq b c z z]

end ArakelovGeometry

end

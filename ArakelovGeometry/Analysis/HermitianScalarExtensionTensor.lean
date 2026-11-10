/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.HermitianScalarExtension
import ArakelovGeometry.Analysis.HermitianNorm
import ArakelovGeometry.Analysis.HermitianTensor
import ArakelovGeometry.Analysis.TensorOperator
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Hermitian scalar extension and orthogonal tensor norms

The extended field carries its given absolute-value norm as an inner-product
space over the base field. The Hermitian scalar-extension norm agrees with
the orthogonal tensor norm on the same scalar-extension module.
-/

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

section Binary

variable {k : Type*} [RCLike k] {E : Unit ⊕ Unit → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace k (E i)]
  {κ : Unit ⊕ Unit → Type*} [∀ i, Fintype (κ i)]
  (b : ∀ i, OrthonormalBasis (κ i) k (E i))

/-- The existing finite orthogonal tensor core gives the usual binary
Hilbert tensor pairing under the canonical binary tensor equivalence. -/
theorem orthogonalTensorCore_binary_inner (z t : ⨂[k] i, E i) :
    (orthogonalTensorCore b).inner z t =
      inner k (binaryTensorEquiv k E z) (binaryTensorEquiv k E t) := by
  classical
  let := orthogonalTensorCore b
  induction z using PiTensorProduct.induction_on with
  | add z u hz hu =>
    simp only [InnerProductSpace.Core.inner_add_left, map_add, inner_add_left, hz, hu]
  | smul_tprod r x =>
    induction t using PiTensorProduct.induction_on with
    | add t u ht hu =>
      simp only [InnerProductSpace.Core.inner_add_right, map_add, inner_add_right, ht, hu]
    | smul_tprod s y =>
      simp only [InnerProductSpace.Core.inner_smul_left, InnerProductSpace.Core.inner_smul_right,
        map_smul, inner_smul_right]
      rw [orthogonalTensorCore_tprod, binaryTensorEquiv_tprod,
        binaryTensorEquiv_tprod, TensorProduct.inner_tmul]
      simp

/-- The existing finite orthogonal norm equals Mathlib's binary Hilbert
tensor norm, including zero-dimensional factors. -/
theorem orthogonalTensorSeminorm_binary (z : ⨂[k] i, E i) :
    orthogonalTensorSeminorm b z = ‖binaryTensorEquiv k E z‖ := by
  apply (sq_eq_sq₀ (apply_nonneg _ _) (norm_nonneg _)).mp
  rw [orthogonalTensorSeminorm_sq, orthogonalTensorCore_binary_inner,
    norm_sq_eq_re_inner (𝕜 := k)]

end Binary

section ScalarExtension

variable {k L : Type*} [RCLike k] [RCLike L] [NormedAlgebra k L]

/-- The given absolute-value norm of an extended real or complex field
is Hermitian for the existing base-field scalar action. -/
abbrev normedAlgebraInnerProductSpace : InnerProductSpace k L :=
  InnerProductSpace.ofNorm k (InnerProductSpaceable.parallelogram_identity (E := L))

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace k E]
  [Fintype ι] (b : OrthonormalBasis ι k E)

/-- The exact Hermitian scalar-extension norm is the orthogonal binary
tensor norm with the given absolute value on the extended field. -/
theorem hermitianScalarExtensionSeminorm_eq_tensor_norm (z : L ⊗[k] E) :
    let := normedAlgebraInnerProductSpace (k := k) (L := L)
    hermitianScalarExtensionSeminorm b z = ‖z‖ := by
  intro iL
  let := iL
  classical
  have hz : z = ∑ i, hermitianScalarExtensionCoordinates b z i ⊗ₜ[k] b i := by
    symm
    change (∑ i, (b.toBasis.baseChange L).repr z i ⊗ₜ[k] b i) = z
    simpa only [Module.Basis.baseChange_apply, OrthonormalBasis.coe_toBasis,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      (b.toBasis.baseChange L).sum_repr z
  change ‖hermitianScalarExtensionCoordinates b z‖ = ‖z‖
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, norm_sq_eq_re_inner (𝕜 := k)]
  conv_rhs => rw [hz]
  simp only [sum_inner, inner_sum, TensorProduct.inner_tmul,
    OrthonormalBasis.inner_eq_ite, map_sum]
  simp [apply_ite]

end ScalarExtension

end ArakelovGeometry

end

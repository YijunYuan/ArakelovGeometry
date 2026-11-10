/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.HermitianNorm
public import ArakelovGeometry.Analysis.HermitianScalarExtension
public import ArakelovGeometry.Analysis.ScalarExtensionDual
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Duality for Hermitian scalar extension

Orthonormal coordinates compute actual operator norms. They identify the
Hermitian extension of the dual with the dual of the Hermitian extension.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

variable {k E ι : Type*} [RCLike k] [NormedAddCommGroup E] [InnerProductSpace k E]
  [FiniteDimensional k E] [Fintype ι] (b : OrthonormalBasis ι k E)

/-- The actual operator norm of an algebraic functional is the Euclidean
norm of its values on any orthonormal basis, including the empty basis. -/
theorem linearMapOperatorSeminorm_sq_eq_sum_orthonormal (f : E →ₗ[k] k) :
    (linearMapOperatorSeminorm f) ^ 2 = ∑ i, ‖f (b i)‖ ^ 2 := by
  let : CompleteSpace E := FiniteDimensional.complete k E
  let g := LinearMap.toContinuousLinearMap f
  have hn : linearMapOperatorSeminorm f = ‖g‖ :=
    linearMapOperatorSeminorm_coe_continuousLinearMap g
  rw [hn, ← (InnerProductSpace.toDual k E).symm.norm_map g,
    ← b.sum_sq_norm_inner_left]
  simp only [InnerProductSpace.toDual_symm_apply]
  rfl

/-- Dual-basis coordinates identify the actual algebraic dual with a
Euclidean coordinate space. -/
def hermitianDualCoordinates : Module.Dual k E ≃ₗ[k] EuclideanSpace k ι := by
  classical
  exact b.toBasis.dualBasis.equivFun.trans (WithLp.linearEquiv 2 k (ι → k)).symm

omit [FiniteDimensional k E] in
/-- Dual coordinates evaluate the functional at the original basis vector. -/
theorem hermitianDualCoordinates_apply (f : Module.Dual k E) (i : ι) :
    hermitianDualCoordinates b f i = f (b i) := by
  classical
  exact b.toBasis.dualBasis_equivFun f i

/-- Dual-basis Euclidean coordinates carry precisely the existing
operator norm, rather than a separately prescribed norm. -/
theorem hermitianDualCoordinates_norm (f : Module.Dual k E) :
    ‖hermitianDualCoordinates b f‖ = linearMapOperatorSeminorm f := by
  apply (sq_eq_sq₀ (norm_nonneg _) (apply_nonneg _ _)).mp
  rw [EuclideanSpace.norm_sq_eq, linearMapOperatorSeminorm_sq_eq_sum_orthonormal b]
  simp only [hermitianDualCoordinates_apply]

/-- The dual coordinate equivalence is an isometry for the actual
operator norm on the algebraic dual. -/
def hermitianDualIsometry :
    let := linearDualNormedAddCommGroup (k := k) (E := E)
    let := linearDualNormedSpace (k := k) (E := E)
    Module.Dual k E ≃ₗᵢ[k] EuclideanSpace k ι := by
  intro nD nsD
  let := nD
  let := nsD
  exact { hermitianDualCoordinates b with norm_map' := hermitianDualCoordinates_norm b }

variable {L : Type*} [RCLike L] [NormedAlgebra k L]

/-- Install the separated Hermitian norm on the actual tensor extension. -/
abbrev hermitianScalarExtensionNormedAddCommGroup : NormedAddCommGroup (L ⊗[k] E) :=
  (⟨(hermitianScalarExtensionSeminorm (L := L) b).toAddGroupSeminorm,
    fun z ↦ (hermitianScalarExtensionSeminorm_eq_zero_iff b z).mp⟩ :
    AddGroupNorm (L ⊗[k] E)).toNormedAddCommGroup

/-- Its normed-space structure keeps the canonical extended scalar action. -/
abbrev hermitianScalarExtensionNormedSpace :
    let := hermitianScalarExtensionNormedAddCommGroup (L := L) b
    NormedSpace L (L ⊗[k] E) := by
  let := hermitianScalarExtensionNormedAddCommGroup (L := L) b
  exact ⟨fun a z ↦ (map_smul_eq_mul (hermitianScalarExtensionSeminorm b) a z).le⟩

/-- The exact extended pairing induces the installed Hermitian norm. -/
abbrev hermitianScalarExtensionInnerProductSpace :
    let := hermitianScalarExtensionNormedAddCommGroup (L := L) b
    let := hermitianScalarExtensionNormedSpace (L := L) b
    InnerProductSpace L (L ⊗[k] E) := by
  intro nG nsG
  let := nG
  let := nsG
  exact innerProductSpaceOfCoreNorm (hermitianScalarExtensionCore (L := L) b)
    (hermitianScalarExtensionSeminorm_sq b)

/-- Scalar extension of the original orthonormal basis is orthonormal for
the exact extended pairing and norm. -/
def hermitianScalarExtensionOrthonormalBasis :
    let := hermitianScalarExtensionNormedAddCommGroup (L := L) b
    let := hermitianScalarExtensionNormedSpace (L := L) b
    let := hermitianScalarExtensionInnerProductSpace (L := L) b
    OrthonormalBasis ι L (L ⊗[k] E) := by
  intro nG nsG iG
  let := nG
  let := nsG
  let := iG
  exact ⟨{ hermitianScalarExtensionCoordinates (L := L) b with norm_map' := fun _ ↦ rfl }⟩

omit [FiniteDimensional k E] in
/-- The extended orthonormal basis consists of the actual rational tensors. -/
theorem hermitianScalarExtensionOrthonormalBasis_apply (i : ι) :
    hermitianScalarExtensionOrthonormalBasis (L := L) b i = (1 : L) ⊗ₜ[k] (b i) := by
  classical
  let := hermitianScalarExtensionNormedAddCommGroup (L := L) b
  let := hermitianScalarExtensionNormedSpace (L := L) b
  let := hermitianScalarExtensionInnerProductSpace (L := L) b
  apply (hermitianScalarExtensionCoordinates (L := L) b).injective
  change (hermitianScalarExtensionOrthonormalBasis b).repr
      (hermitianScalarExtensionOrthonormalBasis b i) = _
  rw [OrthonormalBasis.repr_self]
  ext j
  simp only [hermitianScalarExtensionCoordinates_tmul, one_mul,
    OrthonormalBasis.repr_self, PiLp.single_apply]
  split_ifs <;> simp_all

/-- Hermitian scalar extension commutes with any actual realization of the
normed dual. The sole transport hypothesis identifies the original norm with
the original operator norm; the extended norm equality is the conclusion. -/
theorem hermitianScalarExtension_dual_transport {A κ : Type*}
    [NormedAddCommGroup A] [InnerProductSpace k A] [Fintype κ]
    (c : OrthonormalBasis κ k A) (e : A ≃ₗ[k] Module.Dual k E)
    (he : ∀ x, ‖x‖ = linearMapOperatorSeminorm (e x)) (z : L ⊗[k] A) :
    let := hermitianScalarExtensionNormedAddCommGroup (L := L) b
    let := hermitianScalarExtensionNormedSpace (L := L) b
    linearMapOperatorSeminorm
      (dualBaseChangeEquiv k L E (e.toLinearMap.baseChange L z)) =
        hermitianScalarExtensionSeminorm c z := by
  intro nG nsG
  let := nG
  let := nsG
  let := hermitianScalarExtensionInnerProductSpace (L := L) b
  let d : A ≃ₗᵢ[k] EuclideanSpace k ι :=
    { e.trans (hermitianDualCoordinates b) with
      norm_map' := fun x ↦ (hermitianDualCoordinates_norm b (e x)).trans (he x).symm }
  let c' : OrthonormalBasis ι k A := ⟨d⟩
  have heval (t : L ⊗[k] A) (i : ι) :
      hermitianScalarExtensionCoordinates c' t i =
        dualBaseChangeEquiv k L E (e.toLinearMap.baseChange L t) (1 ⊗ₜ[k] b i) := by
    induction t using TensorProduct.inductionOn with
    | add t u ht hu => simp [map_add, ht, hu]
    | tmul a x =>
      rw [hermitianScalarExtensionCoordinates_tmul, LinearMap.baseChange_tmul,
        dualBaseChangeEquiv_tmul_one]
      congr 2
      exact hermitianDualCoordinates_apply b (e x) i
  rw [hermitianScalarExtensionSeminorm_eq c c']
  apply (sq_eq_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [linearMapOperatorSeminorm_sq_eq_sum_orthonormal
    (hermitianScalarExtensionOrthonormalBasis (L := L) b)]
  change (∑ i, ‖_‖ ^ 2) = ‖hermitianScalarExtensionCoordinates c' z‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [hermitianScalarExtensionOrthonormalBasis_apply, ← heval]

/-- The duality identity as a ratio supremum of the actual extended
pairing. This form transports directly along completed-fibre equivalences. -/
theorem hermitianScalarExtension_dual_eq_sSup {A κ : Type*}
    [NormedAddCommGroup A] [InnerProductSpace k A] [Fintype κ]
    (c : OrthonormalBasis κ k A) (e : A ≃ₗ[k] Module.Dual k E)
    (he : ∀ x, ‖x‖ = linearMapOperatorSeminorm (e x)) (z : L ⊗[k] A) :
    hermitianScalarExtensionSeminorm c z =
      sSup (Set.range fun t : L ⊗[k] E ↦
        ‖dualBaseChangeEquiv k L E (e.toLinearMap.baseChange L z) t‖ /
          hermitianScalarExtensionSeminorm b t) := by
  let := hermitianScalarExtensionNormedAddCommGroup (L := L) b
  let := hermitianScalarExtensionNormedSpace (L := L) b
  exact (hermitianScalarExtension_dual_transport b c e he z).symm.trans
    (linearMapOperatorSeminorm_eq_sSup _)

end ArakelovGeometry

end

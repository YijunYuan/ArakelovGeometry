/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.CompactPositiveCone
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Compact cones of contact matrices

The real trace pairing on the actual subspace of Hermitian matrices identifies
its real dual. Rank-one matrices from a compact set of unit vectors then form a
compact trace-one base, so their finite conical hull is closed and admits a
Hermitian separating matrix when it does not contain the identity.
-/

open Matrix
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

noncomputable section

namespace ArakelovGeometry

variable {L n : Type*} [RCLike L] [Fintype n]

/-- The real trace pairing on the canonical real submodule of Hermitian matrices. -/
def hermitianTracePairing :
    LinearMap.BilinForm ℝ (selfAdjoint.submodule ℝ (Matrix n n L)) where
  toFun H :=
    { toFun := fun J => RCLike.re (((H : Matrix n n L) * J).trace)
      map_add' := by intros; simp [Matrix.mul_add]
      map_smul' := by
        intro r J
        simp [RCLike.smul_re] }
  map_add' := by intros; ext; simp [Matrix.add_mul]
  map_smul' := by
    intro r H
    ext J
    simp [RCLike.smul_re]

/-- Positivity of the trace of a square makes the trace pairing definite. -/
theorem hermitianTracePairing_self_eq_zero (H : selfAdjoint.submodule ℝ (Matrix n n L))
    (hH : hermitianTracePairing H H = 0) : H = 0 := by
  have hstar : (H : Matrix n n L)ᴴ = H := H.property
  have hnonneg := (Matrix.posSemidef_conjTranspose_mul_self (H : Matrix n n L)).trace_nonneg
  have hre : RCLike.re (((H : Matrix n n L)ᴴ * H).trace) = 0 := by
    simpa only [hstar] using (show RCLike.re (((H : Matrix n n L) * H).trace) = 0 from hH)
  have hz : ((H : Matrix n n L)ᴴ * H).trace = 0 :=
    RCLike.ext (by simpa using hre) (by simpa using (RCLike.nonneg_iff.mp hnonneg).2)
  exact Subtype.ext (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz)

/-- The trace pairing is nondegenerate on the actual Hermitian subspace. -/
theorem hermitianTracePairing_nondegenerate :
    (hermitianTracePairing (L := L) (n := n)).Nondegenerate := by
  constructor
  · intro H hH
    exact hermitianTracePairing_self_eq_zero H (hH H)
  · intro H hH
    exact hermitianTracePairing_self_eq_zero H (hH H)

/-- Every real linear functional on Hermitian matrices is represented by a
Hermitian matrix through the trace pairing. -/
theorem exists_hermitian_trace_representation
    (f : (selfAdjoint.submodule ℝ (Matrix n n L)) →ₗ[ℝ] ℝ) :
    ∃ H : selfAdjoint.submodule ℝ (Matrix n n L),
      ∀ J : selfAdjoint.submodule ℝ (Matrix n n L),
        f J = RCLike.re (((H : Matrix n n L) * J).trace) := by
  let e := (hermitianTracePairing (L := L) (n := n)).toDual
    hermitianTracePairing_nondegenerate
  refine ⟨e.symm f, fun J => ?_⟩
  have h := congrArg (fun g : Module.Dual ℝ (selfAdjoint.submodule ℝ (Matrix n n L)) =>
    g J) (e.apply_symm_apply f)
  exact h.symm

/-- The rank-one contact matrix `u u*`, as an element of the Hermitian subspace. -/
def contactMatrix (u : EuclideanSpace L n) : selfAdjoint.submodule ℝ (Matrix n n L) :=
  ⟨Matrix.vecMulVec u.ofLp (star u.ofLp), by
    change (Matrix.vecMulVec u.ofLp (star u.ofLp))ᴴ = _
    simp only [Matrix.conjTranspose_vecMulVec, star_star]⟩

omit [Fintype n] in
/-- Contact matrices vary continuously in the actual Euclidean vector. -/
theorem continuous_contactMatrix : Continuous (contactMatrix (L := L) (n := n)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (PiLp.continuous_apply 2 _ i).mul ((PiLp.continuous_apply 2 _ j).star)

/-- The trace of a contact matrix is the squared Euclidean norm. -/
theorem trace_contactMatrix (u : EuclideanSpace L n) :
    ((contactMatrix u : selfAdjoint.submodule ℝ (Matrix n n L)) : Matrix n n L).trace =
      algebraMap ℝ L (‖u‖ ^ 2) := by
  change (Matrix.vecMulVec u.ofLp (star u.ofLp)).trace = _
  rw [Matrix.trace_vecMulVec, EuclideanSpace.norm_sq_eq, map_sum]
  simp only [dotProduct, Pi.star_apply, map_pow]
  apply Finset.sum_congr rfl
  intro i _
  exact RCLike.mul_conj (u.ofLp i)

/-- Pairing two rank-one contact matrices gives the squared absolute inner product. -/
theorem hermitianTracePairing_contact_contact (u v : EuclideanSpace L n) :
    hermitianTracePairing (contactMatrix u) (contactMatrix v) = ‖inner L u v‖ ^ 2 := by
  change RCLike.re ((Matrix.vecMulVec u.ofLp (star u.ofLp) *
    Matrix.vecMulVec v.ofLp (star v.ofLp)).trace) = _
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul,
    smul_eq_mul, dotProduct_comm (star u.ofLp) v.ofLp,
    ← EuclideanSpace.inner_eq_star_dotProduct, ← EuclideanSpace.inner_eq_star_dotProduct,
    ← inner_conj_symm v u, RCLike.mul_conj]
  simp only [← map_pow, RCLike.ofReal_re]

/-- Real trace as a continuous functional on Hermitian matrices. -/
def hermitianTrace : (selfAdjoint.submodule ℝ (Matrix n n L)) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (RCLike.reLm.comp ((Matrix.traceLinearMap n ℝ L).comp
      (selfAdjoint.submodule ℝ (Matrix n n L)).subtype))

/-- The contact matrix of a unit vector has real trace one. -/
theorem hermitianTrace_contactMatrix (u : EuclideanSpace L n) :
    hermitianTrace (contactMatrix u) = ‖u‖ ^ 2 := by
  change RCLike.re ((contactMatrix u : Matrix n n L).trace) = _
  rw [trace_contactMatrix]
  exact RCLike.ofReal_re _

/-- The actual finite cone generated by a compact nonempty set of unit contact
matrices is closed; no closure is inserted into the cone's definition. -/
theorem isClosed_contactMatrix_cone {D : Set (EuclideanSpace L n)} (hD : IsCompact D)
    (hne : D.Nonempty) (hunit : ∀ u ∈ D, ‖u‖ = 1) :
    IsClosed (PointedCone.hull ℝ (contactMatrix '' D) :
      Set (selfAdjoint.submodule ℝ (Matrix n n L))) := by
  have hf : ∀ J ∈ contactMatrix '' D, hermitianTrace J = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hermitianTrace_contactMatrix, hunit u hu, one_pow]
  exact isClosed_pointedCone_hull_of_compact_base
    (hD.image continuous_contactMatrix) (hne.image contactMatrix) hermitianTrace hf

variable [DecidableEq n]

/-- The identity matrix in the canonical Hermitian subspace. -/
def hermitianIdentity : selfAdjoint.submodule ℝ (Matrix n n L) :=
  ⟨1, by change (1 : Matrix n n L)ᴴ = 1; exact Matrix.conjTranspose_one⟩

/-- Trace pairing against a contact matrix is the genuine Hermitian quadratic
form on its generating Euclidean vector. -/
theorem hermitianTracePairing_contactMatrix
    (H : selfAdjoint.submodule ℝ (Matrix n n L)) (u : EuclideanSpace L n) :
    hermitianTracePairing H (contactMatrix u) =
      RCLike.re (inner L u ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) H u)) := by
  change RCLike.re (((H : Matrix n n L) * Matrix.vecMulVec u.ofLp (star u.ofLp)).trace) = _
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]

/-- If the identity is outside a compact contact cone, a genuine Hermitian
matrix has positive trace and nonpositive quadratic form on every contact. -/
theorem exists_hermitian_separating_contact_matrix {D : Set (EuclideanSpace L n)}
    (hD : IsCompact D) (hne : D.Nonempty) (hunit : ∀ u ∈ D, ‖u‖ = 1)
    (hI : hermitianIdentity (L := L) (n := n) ∉ PointedCone.hull ℝ (contactMatrix '' D)) :
    ∃ H : Matrix n n L, H.IsHermitian ∧ 0 < RCLike.re H.trace ∧
      ∀ u ∈ D, RCLike.re (inner L u
        ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) H u)) ≤ 0 := by
  have hf : ∀ J ∈ contactMatrix '' D, hermitianTrace J = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hermitianTrace_contactMatrix, hunit u hu, one_pow]
  obtain ⟨g, hgI, hgD⟩ := exists_separating_functional_of_not_mem_pointedCone_hull
    (hD.image continuous_contactMatrix) (hne.image contactMatrix) hermitianTrace hf hI
  obtain ⟨H, hH⟩ := exists_hermitian_trace_representation g.toLinearMap
  refine ⟨H, H.property, ?_, ?_⟩
  · rw [show g hermitianIdentity = RCLike.re ((H : Matrix n n L).trace) by
      have ht := hH hermitianIdentity
      change g hermitianIdentity = _ at ht
      simpa only [hermitianIdentity, Matrix.mul_one] using ht] at hgI
    exact hgI
  · intro u hu
    have hg := hgD (contactMatrix u) ⟨u, hu, rfl⟩
    rw [show g (contactMatrix u) = hermitianTracePairing H (contactMatrix u) from
      hH (contactMatrix u), hermitianTracePairing_contactMatrix] at hg
    exact hg

/-- A contact-cone decomposition of the identity gives the dimension-sharp
Euclidean bound, including the zero-dimensional case. -/
theorem norm_sq_le_card_of_identity_mem_contact_cone {D : Set (EuclideanSpace L n)}
    (hunit : ∀ u ∈ D, ‖u‖ = 1)
    (hI : hermitianIdentity (L := L) (n := n) ∈ PointedCone.hull ℝ (contactMatrix '' D))
    (x : EuclideanSpace L n) (hx : ∀ u ∈ D, ‖inner L u x‖ ≤ 1) :
    ‖x‖ ^ 2 ≤ Fintype.card n := by
  have hcone : ∀ J ∈ PointedCone.hull ℝ (contactMatrix '' D),
      hermitianTracePairing J (contactMatrix x) ≤ hermitianTrace J := by
    intro J hJ
    induction hJ using Submodule.span_induction with
    | mem J hJ =>
      obtain ⟨u, hu, rfl⟩ := hJ
      rw [hermitianTracePairing_contact_contact, hermitianTrace_contactMatrix, hunit u hu]
      exact pow_le_pow_left₀ (norm_nonneg _) (hx u hu) 2
    | zero => simp
    | add J K _ _ hJ hK => simpa using add_le_add hJ hK
    | smul a J _ hJ =>
      change hermitianTracePairing ((a : ℝ) • J) (contactMatrix x) ≤
        hermitianTrace ((a : ℝ) • J)
      rw [map_smul, LinearMap.smul_apply, map_smul]
      exact mul_le_mul_of_nonneg_left hJ a.property
  have h := hcone hermitianIdentity hI
  change RCLike.re (((1 : Matrix n n L) * contactMatrix x).trace) ≤
    RCLike.re ((1 : Matrix n n L).trace) at h
  simpa only [Matrix.one_mul, trace_contactMatrix, Matrix.trace_one,
    RCLike.algebraMap_eq_ofReal, RCLike.ofReal_re, RCLike.natCast_re] using h

/-- The square-root dimension bound follows from the actual identity decomposition. -/
theorem norm_le_sqrt_card_of_identity_mem_contact_cone {D : Set (EuclideanSpace L n)}
    (hunit : ∀ u ∈ D, ‖u‖ = 1)
    (hI : hermitianIdentity (L := L) (n := n) ∈ PointedCone.hull ℝ (contactMatrix '' D))
    (x : EuclideanSpace L n) (hx : ∀ u ∈ D, ‖inner L u x‖ ≤ 1) :
    ‖x‖ ≤ Real.sqrt (Fintype.card n) :=
  Real.le_sqrt_of_sq_le (norm_sq_le_card_of_identity_mem_contact_cone hunit hI x hx)

end ArakelovGeometry

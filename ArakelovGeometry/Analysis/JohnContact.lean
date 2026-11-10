/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.EllipsoidPerturbation

/-!
# Contact decomposition of a maximal ellipsoid

For a compact polar body inside the Euclidean unit ball, maximality of the
identity ellipsoid forces the identity into the finite cone of unit contact
matrices. The separating matrix is perturbed by a small scalar identity and
then produces a strictly larger feasible positive ellipsoid, a contradiction.
-/

open Matrix
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

noncomputable section

namespace ArakelovGeometry

variable {L n : Type*} [RCLike L] [Fintype n] [DecidableEq n]

/-- In positive dimension a compact polar with maximal identity ellipsoid has
at least one actual unit contact. -/
theorem unit_contacts_nonempty_of_maximal [Nonempty n]
    {D : Set (EuclideanSpace L n)} (hD : IsCompact D) (hball : ∀ x ∈ D, ‖x‖ ≤ 1)
    (hmax : ∀ A : Matrix n n L, A.PosDef →
      (∀ x ∈ D, ‖(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A x‖ ≤ 1) →
      RCLike.re A.det ≤ 1) :
    (D ∩ {x | ‖x‖ = 1}).Nonempty := by
  by_contra hnone
  have htrace : 0 < RCLike.re ((1 : Matrix n n L).trace) := by
    simpa only [Matrix.trace_one, RCLike.natCast_re] using
      (Nat.cast_pos.mpr (Fintype.card_pos (α := n)) : (0 : ℝ) < Fintype.card n)
  have hin : ∀ x ∈ D, ‖x‖ = 1 →
      RCLike.re (inner L x ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) 1 x)) < 0 := by
    intro x hx hn
    exact (hnone ⟨x, hx, hn⟩).elim
  obtain ⟨A, hA, hdet, hAD⟩ := exists_larger_ellipsoid_of_inward_direction hD hball
    1 Matrix.isHermitian_one htrace hin
  exact (not_lt_of_ge (hmax A hA hAD)) hdet

/-- Subtracting a real scalar identity acts on actual Euclidean vectors by scalar subtraction. -/
theorem toEuclideanCLM_sub_real_smul_one (H : Matrix n n L) (t : ℝ)
    (x : EuclideanSpace L n) :
    (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) (H - (algebraMap ℝ L t) • 1) x =
      (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) H x - (algebraMap ℝ L t) • x := by
  let e := (Matrix.toEuclideanCLM (𝕜 := L) (n := n)).toAlgEquiv.toLinearMap
  have hone : e 1 = 1 := map_one (Matrix.toEuclideanCLM (𝕜 := L) (n := n))
  change (e (H - (algebraMap ℝ L t) • 1)) x = _
  rw [map_sub, map_smul, hone]
  rfl

/-- Positive-trace weak separation of unit contacts can be made strict while
retaining positive trace, using the actual scalar identity matrix. -/
theorem exists_strict_inward_hermitian_direction [Nonempty n]
    {D : Set (EuclideanSpace L n)} (H : Matrix n n L) (hH : H.IsHermitian)
    (htrace : 0 < RCLike.re H.trace)
    (hsep : ∀ x ∈ D, ‖x‖ = 1 →
      RCLike.re (inner L x ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) H x)) ≤ 0) :
    ∃ J : Matrix n n L, J.IsHermitian ∧ 0 < RCLike.re J.trace ∧
      ∀ x ∈ D, ‖x‖ = 1 →
        RCLike.re (inner L x ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) J x)) < 0 := by
  let r : ℝ := Fintype.card n
  have hr : 0 < r := Nat.cast_pos.mpr (Fintype.card_pos (α := n))
  let δ : ℝ := RCLike.re H.trace / (2 * r)
  have hδ : 0 < δ := div_pos htrace (mul_pos (by norm_num) hr)
  have hδr : δ * r = RCLike.re H.trace / 2 := by
    dsimp [δ]
    field_simp
  let J : Matrix n n L := H - (algebraMap ℝ L δ) • 1
  have hself : IsSelfAdjoint (algebraMap ℝ L δ) := by simp [isSelfAdjoint_iff]
  refine ⟨J, hH.sub (Matrix.isHermitian_one.smul hself), ?_, ?_⟩
  · change 0 < RCLike.re (H - (algebraMap ℝ L δ) • (1 : Matrix n n L)).trace
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, map_sub, smul_eq_mul,
      RCLike.algebraMap_eq_ofReal, RCLike.re_ofReal_mul, RCLike.natCast_re]
    change 0 < RCLike.re H.trace - δ * r
    linarith
  · intro x hx hn
    change RCLike.re (inner L x ((Matrix.toEuclideanCLM (𝕜 := L) (n := n))
      (H - (algebraMap ℝ L δ) • 1) x)) < 0
    rw [toEuclideanCLM_sub_real_smul_one, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hn]
    simp only [RCLike.ofReal_one, one_pow, mul_one, map_sub,
      RCLike.algebraMap_eq_ofReal, RCLike.ofReal_re]
    linarith [hsep x hx hn]

/-- Maximality forces the actual identity matrix into the finite contact cone.
No contact decomposition or identity-membership hypothesis is assumed. -/
theorem identity_mem_contact_cone_of_maximal {D : Set (EuclideanSpace L n)}
    (hD : IsCompact D) (hball : ∀ x ∈ D, ‖x‖ ≤ 1)
    (hmax : ∀ A : Matrix n n L, A.PosDef →
      (∀ x ∈ D, ‖(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A x‖ ≤ 1) →
      RCLike.re A.det ≤ 1) :
    hermitianIdentity (L := L) (n := n) ∈
      PointedCone.hull ℝ (contactMatrix '' (D ∩ {x | ‖x‖ = 1})) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hzero : hermitianIdentity (L := L) (n := n) = 0 := Subsingleton.elim _ _
    rw [hzero]
    exact Submodule.zero_mem _
  · by_contra hI
    have hc : IsCompact (D ∩ {x | ‖x‖ = 1}) :=
      hD.inter_right (isClosed_eq continuous_norm continuous_const)
    obtain ⟨H, hH, htrace, hsep⟩ := exists_hermitian_separating_contact_matrix hc
      (unit_contacts_nonempty_of_maximal hD hball hmax) (fun _ hx => hx.2) hI
    obtain ⟨J, hJ, hJtrace, hJin⟩ := exists_strict_inward_hermitian_direction H hH htrace
      (fun x hx hn => hsep x ⟨hx, hn⟩)
    obtain ⟨A, hA, hdet, hAD⟩ := exists_larger_ellipsoid_of_inward_direction
      hD hball J hJ hJtrace hJin
    exact (not_lt_of_ge (hmax A hA hAD)) hdet

/-- The dimension-sharp norm bound is now a consequence of actual maximality,
with identity membership supplied by the perturbation argument. -/
theorem norm_le_sqrt_card_of_maximal_polar {D : Set (EuclideanSpace L n)}
    (hD : IsCompact D) (hball : ∀ x ∈ D, ‖x‖ ≤ 1)
    (hmax : ∀ A : Matrix n n L, A.PosDef →
      (∀ x ∈ D, ‖(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A x‖ ≤ 1) →
      RCLike.re A.det ≤ 1)
    (x : EuclideanSpace L n) (hx : ∀ u ∈ D, ‖inner L u x‖ ≤ 1) :
    ‖x‖ ≤ Real.sqrt (Fintype.card n) :=
  norm_le_sqrt_card_of_identity_mem_contact_cone (fun _ hu => hu.2)
    (identity_mem_contact_cone_of_maximal hD hball hmax) x (fun u hu => hx u hu.1)

end ArakelovGeometry

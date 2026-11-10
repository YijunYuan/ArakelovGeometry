/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.HilbertPolar

/-!
# Dimension-sharp Hermitian norm comparison

The positive determinant optimizer and its actual polar contact decomposition
give a Hermitian norm between the original norm and its square-root-dimension
multiple. The scalar field is real or complex with its usual absolute value.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

noncomputable section

namespace ArakelovGeometry

variable {L E n : Type*} [RCLike L] [NormedAddCommGroup E] [NormedSpace L E]
  [Fintype n] [DecidableEq n]

/-- An invertible matrix acts by the canonical continuous linear equivalence
associated with its actual Euclidean operator. -/
def matrixEuclideanEquiv (A : Matrix n n L) (hA : IsUnit A) :
    EuclideanSpace L n ≃L[L] EuclideanSpace L n :=
  ContinuousLinearEquiv.unitsEquiv L (EuclideanSpace L n)
    ((hA.map (Matrix.toEuclideanCLM (𝕜 := L) (n := n))).unit)

@[simp]
theorem matrixEuclideanEquiv_apply (A : Matrix n n L) (hA : IsUnit A)
    (x : EuclideanSpace L n) :
    matrixEuclideanEquiv A hA x = (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A x := by
  simp only [matrixEuclideanEquiv, ContinuousLinearEquiv.unitsEquiv_apply, IsUnit.unit_spec]

omit [DecidableEq n] in
/-- Normalizing coordinates transports the actual original norm ball by preimage. -/
theorem unitBallInCoordinates_trans_symm (e : E ≃L[L] EuclideanSpace L n)
    (a : EuclideanSpace L n ≃L[L] EuclideanSpace L n) :
    unitBallInCoordinates (e.trans a.symm) = a ⁻¹' unitBallInCoordinates e := by
  ext x
  rfl

omit [DecidableEq n] in
/-- Inclusion of the Euclidean ball proves the lower comparison with the original norm. -/
theorem norm_le_coordinates_of_unitBall_subset (e : E ≃L[L] EuclideanSpace L n)
    (h : Metric.closedBall 0 1 ⊆ unitBallInCoordinates e) (x : E) : ‖x‖ ≤ ‖e x‖ := by
  have hn : ‖e.symm.toContinuousLinearMap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one (fun y hy =>
      h (by simpa only [Metric.mem_closedBall, dist_zero_right, hy] using (le_refl (1 : ℝ))))
  calc
    ‖x‖ = ‖e.symm (e x)‖ := congrArg norm (e.symm_apply_apply x).symm
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ := e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ 1 * ‖e x‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = _ := one_mul _

omit [DecidableEq n] in
/-- A Euclidean bound on the coordinate unit ball proves the upper norm comparison. -/
theorem coordinates_le_mul_norm_of_unitBall_bound (e : E ≃L[L] EuclideanSpace L n)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ y ∈ unitBallInCoordinates e, ‖y‖ ≤ C) (x : E) :
    ‖e x‖ ≤ C * ‖x‖ := by
  have hn : ‖e.toContinuousLinearMap‖ ≤ C :=
    ContinuousLinearMap.opNorm_le_of_unit_norm hC (fun y hy =>
      h (e y) (by change ‖e.symm (e y)‖ ≤ 1; simpa only [e.symm_apply_apply] using hy.le))
  exact (e.toContinuousLinearMap.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

omit [DecidableEq n] in
/-- Every original norm admits actual Hilbert coordinates with the sharp real
or complex square-root-dimension comparison. Dimension zero is included. -/
theorem exists_john_coordinates (e : E ≃L[L] EuclideanSpace L n) :
    ∃ f : E ≃L[L] EuclideanSpace L n, ∀ x : E,
      ‖x‖ ≤ ‖f x‖ ∧ ‖f x‖ ≤ Real.sqrt (Fintype.card n) * ‖x‖ := by
  classical
  obtain ⟨c, hc, hball⟩ := exists_closedBall_subset_unitBallInCoordinates e
  obtain ⟨A, hA, hAB, hmax⟩ := exists_maximal_positiveEllipsoidMatrix
    (isCompact_unitBallInCoordinates e) hc hball
  let a := matrixEuclideanEquiv A hA.isUnit
  let f := e.trans a.symm
  have hbody : unitBallInCoordinates f =
      (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A ⁻¹' unitBallInCoordinates e := by
    rw [show f = e.trans a.symm from rfl, unitBallInCoordinates_trans_symm]
    ext x
    simp only [Set.mem_preimage, a, matrixEuclideanEquiv_apply]
  have hball' : Metric.closedBall 0 1 ⊆ unitBallInCoordinates f := by
    rw [hbody]
    exact unitBall_subset_normalized_ellipsoid_body hAB
  let D := hermitianPolar (L := L) (unitBallInCoordinates f)
  have hD : IsCompact D := isCompact_hermitianPolar_of_unitBall_subset hball'
  have hDball : ∀ x ∈ D, ‖x‖ ≤ 1 := by
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hermitianPolar_subset_unitBall hball' hx
  have hDmax : ∀ M : Matrix n n L, M.PosDef →
      (∀ x ∈ D, ‖(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) M x‖ ≤ 1) →
      RCLike.re M.det ≤ 1 := by
    intro M hM hMD
    apply det_le_one_of_normalized_maximal_ellipsoid hA hmax hM
    refine ⟨hM.posSemidef, ?_⟩
    have hf := (hermitian_ellipsoid_feasible_iff_polar f hM.isHermitian).mpr hMD
    simpa only [hbody] using hf
  have hbound : ∀ y ∈ unitBallInCoordinates f, ‖y‖ ≤ Real.sqrt (Fintype.card n) := by
    intro y hy
    apply norm_le_sqrt_card_of_maximal_polar hD hDball hDmax y
    intro u hu
    exact hu y hy
  refine ⟨f, fun x => ⟨norm_le_coordinates_of_unitBall_subset f hball' x, ?_⟩⟩
  exact coordinates_le_mul_norm_of_unitBall_bound f (Real.sqrt_nonneg _) hbound x

/-- The dimension-sharp real/complex ellipsoid theorem as a positive definite
inner-product core on the original vector space and its original scalar action.
No nonzero-rank hypothesis is needed. -/
theorem exists_john_innerProductCore [FiniteDimensional L E] :
    ∃ c : InnerProductSpace.Core L E, ∀ x : E,
      ‖x‖ ≤ Real.sqrt (RCLike.re (c.inner x x)) ∧
      Real.sqrt (RCLike.re (c.inner x x)) ≤ Real.sqrt (Module.finrank L E) * ‖x‖ := by
  classical
  let e : E ≃L[L] EuclideanSpace L (Fin (Module.finrank L E)) :=
    LinearEquiv.toContinuousLinearEquiv ((Module.finBasis L E).equivFun.trans
      (EuclideanSpace.equiv (Fin (Module.finrank L E)) L).symm.toLinearEquiv)
  obtain ⟨f, hf⟩ := exists_john_coordinates e
  let c : InnerProductSpace.Core L E :=
    { inner := fun x y => inner L (f x) (f y)
      conj_inner_symm := fun x y => inner_conj_symm (f x) (f y)
      re_inner_nonneg := fun x => inner_self_nonneg
      definite := fun x hx => f.injective (by simpa using (inner_self_eq_zero.mp hx))
      add_left := by intros; simp [inner_add_left]
      smul_left := by intros; simp [inner_smul_left] }
  have hc : ∀ x : E, Real.sqrt (RCLike.re (c.inner x x)) = ‖f x‖ := by
    intro x
    change Real.sqrt (RCLike.re (inner L (f x) (f x))) = ‖f x‖
    rw [← norm_sq_eq_re_inner, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨c, fun x => ?_⟩
  rw [hc]
  simpa only [Fintype.card_fin] using hf x

end ArakelovGeometry

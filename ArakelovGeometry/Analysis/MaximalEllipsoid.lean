/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.JohnEllipsoid
import ArakelovGeometry.Analysis.ContactMatrixCone
import Mathlib.Topology.Instances.Matrix

/-!
# Maximal positive ellipsoids

Positive semidefinite matrices whose Euclidean unit-ball image lies in a compact
body form a compact set. An interior Euclidean ball forces a determinant
maximizer to be positive definite. All feasible objects are actual matrices and
actual images of the Euclidean ball.
-/

open Matrix
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

noncomputable section

namespace ArakelovGeometry

variable {L n : Type*} [RCLike L] [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Positivity of Hermitian quadratic forms is a closed matrix condition. -/
theorem isClosed_posSemidef_matrices [Finite n] :
    IsClosed {A : Matrix n n L | A.PosSemidef} := by
  let := Fintype.ofFinite n
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian,
    Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).inter ?_
  apply isClosed_iInter
  intro x
  exact isClosed_le continuous_const
    (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

/-- Matrices of positive ellipsoids contained in an actual Euclidean-coordinate body. -/
def positiveEllipsoidMatrices (B : Set (EuclideanSpace L n)) : Set (Matrix n n L) :=
  {A | A.PosSemidef ∧ ∀ x : EuclideanSpace L n, ‖x‖ ≤ 1 →
    (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A x ∈ B}

/-- The positive-ellipsoid feasibility conditions are closed for a closed body. -/
theorem isClosed_positiveEllipsoidMatrices {B : Set (EuclideanSpace L n)}
    (hB : IsClosed B) : IsClosed (positiveEllipsoidMatrices B) := by
  change IsClosed ({A : Matrix n n L | A.PosSemidef} ∩
    {A | ∀ x : EuclideanSpace L n, ‖x‖ ≤ 1 →
      (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A x ∈ B})
  refine isClosed_posSemidef_matrices.inter ?_
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun x => isClosed_iInter fun _ => ?_
  apply hB.preimage
  have hc := LinearMap.continuous_of_finiteDimensional
    ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)).toAlgEquiv.toLinearMap)
  exact hc.clm_apply continuous_const

/-- A uniform Euclidean bound on the body bounds every entry of a feasible matrix. -/
theorem norm_le_of_mem_positiveEllipsoidMatrices {B : Set (EuclideanSpace L n)}
    {R : ℝ} (hR : 0 ≤ R) (hB : ∀ x ∈ B, ‖x‖ ≤ R)
    {A : Matrix n n L} (hA : A ∈ positiveEllipsoidMatrices B) : ‖A‖ ≤ R := by
  apply (Matrix.norm_le_iff hR).mpr
  intro i j
  have hcol : (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A
      (EuclideanSpace.single j 1) ∈ B :=
    hA.2 _ (by simp only [EuclideanSpace.single, PiLp.norm_single, norm_one, le_refl])
  have hi := PiLp.norm_apply_le
    ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A (EuclideanSpace.single j 1)) i
  have he : ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A
      (EuclideanSpace.single j 1)).ofLp i = A i j := by
    rw [Matrix.ofLp_toEuclideanCLM]
    change (A *ᵥ Pi.single j 1) i = _
    rw [Matrix.mulVec_single_one]
    rfl
  rw [he] at hi
  exact hi.trans (hB _ hcol)

/-- The actual set of feasible positive matrices for a compact body is compact. -/
theorem isCompact_positiveEllipsoidMatrices {B : Set (EuclideanSpace L n)}
    (hB : IsCompact B) : IsCompact (positiveEllipsoidMatrices B) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace L n)).mp
    hB.isBounded
  refine (isCompact_closedBall (0 : Matrix n n L) (max R 0)).of_isClosed_subset
    (isClosed_positiveEllipsoidMatrices hB.isClosed) ?_
  intro A hA
  rw [Metric.mem_closedBall, dist_zero_right]
  apply norm_le_of_mem_positiveEllipsoidMatrices (le_max_right _ _) _ hA
  intro x hx
  exact (show ‖x‖ ≤ R by simpa only [Metric.mem_closedBall, dist_zero_right] using hR hx).trans
    (le_max_left _ _)

/-- A Euclidean ball contained in the body supplies a positive scalar feasible matrix. -/
theorem scalar_mem_positiveEllipsoidMatrices {B : Set (EuclideanSpace L n)}
    {c : ℝ} (hc : 0 ≤ c) (hB : Metric.closedBall 0 c ⊆ B) :
    (algebraMap ℝ L c) • (1 : Matrix n n L) ∈ positiveEllipsoidMatrices B := by
  refine ⟨Matrix.PosSemidef.one.smul (RCLike.ofReal_nonneg.mpr hc), fun x hx => ?_⟩
  apply hB
  rw [Metric.mem_closedBall, dist_zero_right]
  have he : (Matrix.toEuclideanCLM (𝕜 := L) (n := n))
      ((algebraMap ℝ L c) • (1 : Matrix n n L)) x = (algebraMap ℝ L c) • x := by
    change ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)).toAlgEquiv
      ((algebraMap ℝ L c) • (1 : Matrix n n L))) x = _
    rw [← Algebra.algebraMap_eq_smul_one,
      (Matrix.toEuclideanCLM (𝕜 := L) (n := n)).toAlgEquiv.commutes,
      ContinuousLinearMap.algebraMap_apply]
  rw [he, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hc]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hx hc

/-- A compact body containing a positive-radius Euclidean ball has an actual
positive definite matrix of maximal determinant among its positive ellipsoids. -/
theorem exists_maximal_positiveEllipsoidMatrix {B : Set (EuclideanSpace L n)}
    (hB : IsCompact B) {c : ℝ} (hc : 0 < c) (hball : Metric.closedBall 0 c ⊆ B) :
    ∃ A : Matrix n n L, A.PosDef ∧ A ∈ positiveEllipsoidMatrices B ∧
      IsMaxOn (fun M : Matrix n n L => RCLike.re M.det) (positiveEllipsoidMatrices B) A := by
  have hcI : (algebraMap ℝ L c) • (1 : Matrix n n L) ∈ positiveEllipsoidMatrices B :=
    scalar_mem_positiveEllipsoidMatrices hc.le hball
  have hcont : Continuous (fun M : Matrix n n L => RCLike.re M.det) :=
    RCLike.continuous_re.comp continuous_id.matrix_det
  obtain ⟨A, hA, hmax⟩ := (isCompact_positiveEllipsoidMatrices hB).exists_isMaxOn
    ⟨_, hcI⟩ hcont.continuousOn
  refine ⟨A, hA.1.posDef_iff_det_ne_zero.mpr ?_, hA, hmax⟩
  have hpos : 0 < RCLike.re (((algebraMap ℝ L c) • (1 : Matrix n n L)).det) :=
    (RCLike.pos_iff.mp (Matrix.PosDef.one.smul (RCLike.ofReal_pos.mpr hc)).det_pos).1
  have hAdet : 0 < RCLike.re A.det := hpos.trans_le (hmax hcI)
  intro hz
  simp only [hz, map_zero, lt_self_iff_false] at hAdet

/-- Pulling back the body through a feasible matrix includes the Euclidean unit ball. -/
theorem unitBall_subset_normalized_ellipsoid_body {B : Set (EuclideanSpace L n)}
    {A : Matrix n n L} (hA : A ∈ positiveEllipsoidMatrices B) :
    Metric.closedBall 0 1 ⊆ (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A ⁻¹' B := by
  intro x hx
  exact hA.2 x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)

/-- A determinant maximizer normalizes the body so that no positive definite
feasible ellipsoid has determinant greater than one. -/
theorem det_le_one_of_normalized_maximal_ellipsoid {B : Set (EuclideanSpace L n)}
    {A : Matrix n n L} (hA : A.PosDef)
    (hmax : IsMaxOn (fun M : Matrix n n L => RCLike.re M.det)
      (positiveEllipsoidMatrices B) A)
    {M : Matrix n n L} (hM : M.PosDef)
    (hMB : M ∈ positiveEllipsoidMatrices
      ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A ⁻¹' B)) :
    RCLike.re M.det ≤ 1 := by
  have hAM : IsUnit (A * M) := hA.isUnit.mul hM.isUnit
  let P := positivePolarFactor (A * M)
  have hP : P.PosDef := positivePolarFactor_posDef (A * M) hAM
  have hPB : P ∈ positiveEllipsoidMatrices B := by
    refine ⟨hP.posSemidef, fun x hx => ?_⟩
    have him : (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) P x ∈
        (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) (A * M) '' Metric.closedBall 0 1 := by
      rw [← positivePolarFactor_image_closedBall (A * M) hAM]
      exact ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, rfl⟩
    obtain ⟨y, hy, he⟩ := him
    rw [← he]
    simpa only [map_mul, mul_apply_eq_comp, Set.mem_preimage] using
      hMB.2 y (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)
  have hd : RCLike.re P.det ≤ RCLike.re A.det := hmax hPB
  have hdetP : RCLike.re P.det = RCLike.re A.det * RCLike.re M.det := by
    rw [show P = positivePolarFactor (A * M) from rfl, det_positivePolarFactor,
      RCLike.algebraMap_eq_ofReal, RCLike.ofReal_re, Matrix.det_mul, norm_mul]
    have ha : A.det = (RCLike.re A.det : L) :=
      RCLike.ext (by simp) (by simpa using (RCLike.pos_iff.mp hA.det_pos).2)
    have hm : M.det = (RCLike.re M.det : L) :=
      RCLike.ext (by simp) (by simpa using (RCLike.pos_iff.mp hM.det_pos).2)
    conv_lhs => rw [ha, hm]
    rw [RCLike.norm_of_nonneg (RCLike.pos_iff.mp hA.det_pos).1.le,
      RCLike.norm_of_nonneg (RCLike.pos_iff.mp hM.det_pos).1.le]
  rw [hdetP] at hd
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using hd)
    (RCLike.pos_iff.mp hA.det_pos).1

end ArakelovGeometry

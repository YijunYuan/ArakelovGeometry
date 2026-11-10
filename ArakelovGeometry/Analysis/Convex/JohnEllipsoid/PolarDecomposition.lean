/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
# Real and complex ellipsoid infrastructure

The finite Hermitian spectral calculus gives the positive polar factor of an
invertible matrix. This is the local normalization step in the contact-cone
proof of the dimension-sharp ellipsoid bounds.
-/

@[expose] public section

open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace ArakelovGeometry

variable {L n : Type*} [RCLike L] [Fintype n] [DecidableEq n]

/-- The positive polar factor is the canonical square root of `A Aᴴ`. -/
def positivePolarFactor (A : Matrix n n L) : Matrix n n L := CFC.sqrt (A * Aᴴ)

/-- For an invertible matrix the positive polar factor is positive definite. -/
theorem positivePolarFactor_posDef (A : Matrix n n L) (hA : IsUnit A) :
    (positivePolarFactor A).PosDef := by
  have hM := Matrix.PosDef.mul_conjTranspose_self A
    (Matrix.vecMul_injective_iff_isUnit.mpr hA)
  exact (IsStrictlyPositive.sqrt _ hM.isStrictlyPositive).posDef

/-- Squaring the positive polar factor gives the original positive Gram matrix. -/
theorem positivePolarFactor_mul_self (A : Matrix n n L) :
    positivePolarFactor A * positivePolarFactor A = A * Aᴴ :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_self_mul_conjTranspose A).nonneg

/-- Its determinant is exactly the absolute determinant, over either ℝ or ℂ. -/
theorem det_positivePolarFactor (A : Matrix n n L) :
    (positivePolarFactor A).det = algebraMap ℝ L ‖A.det‖ := by
  rw [positivePolarFactor, (Matrix.posSemidef_self_mul_conjTranspose A).det_sqrt,
    Matrix.det_mul, Matrix.det_conjTranspose]
  change RCLike.sqrt (A.det * starRingEnd L A.det) = _
  rw [RCLike.mul_conj, ← map_pow,
    RCLike.sqrt_of_nonneg (RCLike.ofReal_nonneg.mpr (sq_nonneg ‖A.det‖))]
  simp only [RCLike.ofReal_re, Real.sqrt_sq (norm_nonneg _)]

/-- The remaining polar factor is genuinely unitary. -/
theorem inv_positivePolarFactor_mul_mem_unitary (A : Matrix n n L) (hA : IsUnit A) :
    (positivePolarFactor A)⁻¹ * A ∈ Matrix.unitaryGroup n L := by
  let P := positivePolarFactor A
  have hP := positivePolarFactor_posDef A hA
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hP.isHermitian.eq]
  calc
    P⁻¹ * A * (Aᴴ * P⁻¹) = P⁻¹ * (A * Aᴴ) * P⁻¹ := by simp only [mul_assoc]
    _ = P⁻¹ * (P * P) * P⁻¹ := by rw [positivePolarFactor_mul_self]
    _ = 1 := by
      rw [← mul_assoc P⁻¹ P P, Matrix.nonsing_inv_mul P hdet, one_mul,
        Matrix.mul_nonsing_inv P hdet]

/-- A unitary matrix carries the Euclidean closed ball onto itself. -/
theorem unitary_matrix_image_closedBall (U : Matrix n n L)
    (hU : U ∈ Matrix.unitaryGroup n L) (r : ℝ) :
    ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) U) '' Metric.closedBall 0 r =
      Metric.closedBall (0 : EuclideanSpace L n) r := by
  have hU' : U ∈ unitary (Matrix n n L) := hU
  let u : unitary (EuclideanSpace L n →L[L] EuclideanSpace L n) :=
    ⟨(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) U,
      Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) hU'⟩
  let e := Unitary.linearIsometryEquiv u
  have he : (e : EuclideanSpace L n → EuclideanSpace L n) =
      (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) U := by
    exact congrArg (fun f : EuclideanSpace L n →L[L] EuclideanSpace L n =>
      (f : EuclideanSpace L n → EuclideanSpace L n))
      (Unitary.coe_linearIsometryEquiv_apply u)
  rw [← he]
  simpa only [map_zero] using e.image_closedBall 0 r

/-- Replacing an invertible matrix by its positive polar factor preserves the
actual Euclidean ellipsoid, rather than just its volume. -/
theorem positivePolarFactor_image_closedBall (A : Matrix n n L) (hA : IsUnit A)
    (r : ℝ) :
    ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) (positivePolarFactor A)) '' Metric.closedBall 0 r =
      ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A) '' Metric.closedBall 0 r := by
  let P := positivePolarFactor A
  let U := P⁻¹ * A
  have hU : U ∈ Matrix.unitaryGroup n L := inv_positivePolarFactor_mul_mem_unitary A hA
  have hdet : IsUnit P.det :=
    (Matrix.isUnit_iff_isUnit_det P).mp (positivePolarFactor_posDef A hA).isUnit
  have hPU : P * U = A := by
    rw [show P * U = P * (P⁻¹ * A) from rfl, ← mul_assoc,
      Matrix.mul_nonsing_inv P hdet, one_mul]
  calc
    ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) P) '' Metric.closedBall 0 r =
        ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) P) ''
          (((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) U) '' Metric.closedBall 0 r) := by
      rw [unitary_matrix_image_closedBall U hU]
    _ = ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) (P * U)) '' Metric.closedBall 0 r := by
      rw [Set.image_image]
      congr 1
      ext x
      simp only [map_mul, mul_apply_eq_comp]
    _ = ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A) '' Metric.closedBall 0 r := by rw [hPU]

/-- Every invertible real or complex linear image of the Euclidean ball has a
positive definite representative with the same determinant norm. -/
theorem exists_posDef_same_ellipsoid (A : Matrix n n L) (hA : IsUnit A) :
    ∃ P : Matrix n n L, P.PosDef ∧ P.det = algebraMap ℝ L ‖A.det‖ ∧
      ∀ r : ℝ, ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) P) '' Metric.closedBall 0 r =
        ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A) '' Metric.closedBall 0 r :=
  ⟨positivePolarFactor A, positivePolarFactor_posDef A hA,
    det_positivePolarFactor A, positivePolarFactor_image_closedBall A hA⟩

end ArakelovGeometry

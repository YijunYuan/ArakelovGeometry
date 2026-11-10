/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.ComplexPolarization
public import ArakelovGeometry.Analysis.RationalEllipsoid

/-!
# Rational ellipsoids in compatible complex coordinates

A single countable family of complex rational matrix factors works for both
real and complex completed fields. At real places the associated norm is the
restriction of a Euclidean quadratic form to the actual real vector space.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace ArakelovGeometry

variable {L n : Type*} [RCLike L] [Fintype n]

/-- Apply a complex field embedding to the actual Euclidean coordinates. -/
def complexCoordinateMap (σ : L →+* ℂ) :
    EuclideanSpace L n →ₛₗ[σ] EuclideanSpace ℂ n where
  toFun z := WithLp.toLp 2 (fun i => σ (z.ofLp i))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp [smul_eq_mul]

omit [Fintype n] in
@[simp]
theorem complexCoordinateMap_apply (σ : L →+* ℂ) (z : EuclideanSpace L n) (i : n) :
    (complexCoordinateMap σ z).ofLp i = σ (z.ofLp i) := rfl

/-- Coordinate transport preserves the prescribed Euclidean norm. -/
theorem norm_complexCoordinateMap (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (z : EuclideanSpace L n) : ‖complexCoordinateMap σ z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2, complexCoordinateMap_apply, hσ]

omit [Fintype n] in
/-- Rational matrices stay Gaussian rational under either complex orientation;
in the real case their imaginary rational parts vanish. -/
theorem exists_rationalMatrix_map_complex (σ : L →+* ℂ)
    (Q : Matrix n n (ℚ × ℚ)) :
    ∃ P : Matrix n n (ℚ × ℚ), rationalMatrix ℂ P = (rationalMatrix L Q).map σ := by
  rcases RCLike.I_mul_I (K := L) with hI | hI
  · refine ⟨fun i j => ((Q i j).1, 0), ?_⟩
    ext i j
    dsimp [rationalMatrix, Matrix.map, rationalEntry]
    simp [hI]
  · have hs : (σ RCLike.I) ^ 2 = Complex.I ^ 2 := by
      rw [pow_two, ← map_mul, hI, map_neg, map_one, Complex.I_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
    · refine ⟨Q, ?_⟩
      ext i j
      simp [rationalMatrix, rationalEntry, hs]
    · refine ⟨fun i j => ((Q i j).1, -(Q i j).2), ?_⟩
      ext i j
      dsimp [rationalMatrix, Matrix.map, rationalEntry]
      simp [hs]

variable [DecidableEq n]

/-- The coordinate embedding intertwines the actual matrix operators. -/
theorem complexCoordinateMap_matrix (σ : L →+* ℂ) (A : Matrix n n L)
    (z : EuclideanSpace L n) :
    complexCoordinateMap σ ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A z) =
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (A.map σ)
        (complexCoordinateMap σ z) := by
  ext i
  change σ (∑ j, A i j * z.ofLp j) = ∑ j, σ (A i j) * σ (z.ofLp j)
  simp only [map_sum, map_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace L E]

/-- Local strict ellipsoids may be selected from one complex countable family,
independently of whether the original completed field is real or complex. -/
theorem exists_strict_complex_rational_coordinates
    (e : E ≃L[L] EuclideanSpace L n) (σ : L →+* ℂ)
    (hσ : ∀ x, ‖σ x‖ = ‖x‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Q : Matrix n n (ℚ × ℚ)) (δ : ℚ), 0 < δ ∧ ∀ x : E,
      (1 + (δ : ℝ)) * ‖x‖ ^ 2 ≤
        ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (rationalMatrix ℂ Q)
          (complexCoordinateMap σ (e x))‖ ^ 2 ∧
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n)) (rationalMatrix ℂ Q)
        (complexCoordinateMap σ (e x))‖ ^ 2 ≤
          (Fintype.card n + ε - (δ : ℝ)) * ‖x‖ ^ 2 := by
  obtain ⟨P, δ, hδ, hP⟩ := exists_strict_rational_coordinates e hε
  obtain ⟨Q, hQ⟩ := exists_rationalMatrix_map_complex σ P
  refine ⟨Q, δ, hδ, fun x => ?_⟩
  rw [hQ, ← complexCoordinateMap_matrix, norm_complexCoordinateMap σ hσ]
  exact hP x

end ArakelovGeometry

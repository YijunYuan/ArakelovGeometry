/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.NormShape
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Euclidean shape for orthogonal direct sums

The source profile `sqrt (t² + (1-t)²)` is continuous and convex on the
unit interval.  Its homogeneous perspective is `sqrt (a²+b²)` on the
nonnegative quadrant, including the origin.
-/

noncomputable section

namespace ArakelovGeometry.NormShape

private theorem euclidean_profile_eq_norm (t : ℝ) :
    Real.sqrt (t ^ 2 + (1 - t) ^ 2) = ‖WithLp.toLp 2 (t, 1 - t)‖ := by
  simp [WithLp.prod_norm_eq_of_L2, Real.norm_eq_abs]

/-- The Euclidean profile is convex, as the norm of an affine line in the
Euclidean plane. -/
theorem convexOn_euclidean_profile :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => Real.sqrt (t ^ 2 + (1 - t) ^ 2)) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have he : WithLp.toLp 2 (a * x + b * y, 1 - (a * x + b * y)) =
      a • WithLp.toLp 2 (x, 1 - x) + b • WithLp.toLp 2 (y, 1 - y) := by
    apply WithLp.ofLp_injective
    change (a * x + b * y, 1 - (a * x + b * y)) =
      (a * x + b * y, a * (1 - x) + b * (1 - y))
    congr 1
    linear_combination -hab
  simp only [euclidean_profile_eq_norm]
  rw [he]
  calc
    ‖a • WithLp.toLp 2 (x, 1 - x) + b • WithLp.toLp 2 (y, 1 - y)‖ ≤
        ‖a • WithLp.toLp 2 (x, 1 - x)‖ + ‖b • WithLp.toLp 2 (y, 1 - y)‖ :=
      norm_add_le _ _
    _ = a * ‖WithLp.toLp 2 (x, 1 - x)‖ + b * ‖WithLp.toLp 2 (y, 1 - y)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]

/-- The source's Euclidean direct-sum profile. -/
def euclideanShape : NormShape where
  toFun t := Real.sqrt (t ^ 2 + (1 - t) ^ 2)
  continuousOn := by fun_prop
  convexOn := convexOn_euclidean_profile
  lower t ht := by
    apply max_le
    · apply (Real.le_sqrt ht.1 (add_nonneg (sq_nonneg _) (sq_nonneg _))).mpr
      nlinarith [sq_nonneg (1 - t)]
    · apply (Real.le_sqrt (sub_nonneg.mpr ht.2)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))).mpr
      nlinarith [sq_nonneg t]
  upper t ht := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨zero_le_one, ?_⟩
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]

/-- The Euclidean profile's perspective is the Euclidean norm, including
the degenerate point `(0,0)`. -/
theorem euclideanShape_perspective {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    euclideanShape.perspective a b = Real.sqrt (a ^ 2 + b ^ 2) := by
  by_cases hs : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  change (a + b) * Real.sqrt ((a / (a + b)) ^ 2 + (1 - a / (a + b)) ^ 2) = _
  calc
    _ = Real.sqrt ((a + b) ^ 2 *
        ((a / (a + b)) ^ 2 + (1 - a / (a + b)) ^ 2)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (add_nonneg ha hb)]
    _ = Real.sqrt (a ^ 2 + b ^ 2) := by
      congr 1
      field_simp
      ring

/-- Squaring the Euclidean direct-sum norm gives the sum of squares. -/
theorem euclideanShape_perspective_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (euclideanShape.perspective a b) ^ 2 = a ^ 2 + b ^ 2 := by
  rw [euclideanShape_perspective ha hb, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]

end ArakelovGeometry.NormShape

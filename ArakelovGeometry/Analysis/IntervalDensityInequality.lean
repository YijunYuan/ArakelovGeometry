/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.IntervalDensityTransport
import Mathlib.Analysis.MeanInequalities

/-! # The mass inequality for actual interpolated interval transport

The pointwise weighted arithmetic--geometric mean inequality and the actual
mass-matching Jacobian imply the one-dimensional induction step used for
multiplicative convex volume. Endpoint continuity is not needed.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ArakelovGeometry.Analysis.IntervalDensityTransport

/-- The actual weighted Jacobian dominates the normalized mass integrand. -/
theorem weighted_jacobian_geometric {u v A B t : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hA : 0 < A) (hB : 0 < B)
    (ht : t ∈ Icc 0 1) :
    u * (B / A) ^ t ≤
      (1 - t + t * (u * B / (v * A))) * (u ^ (1 - t) * v ^ t) := by
  have hR : 0 < u * B / (v * A) := div_pos (mul_pos hu hB) (mul_pos hv hA)
  have ham := Real.geom_mean_le_arith_mean2_weighted
    (sub_nonneg.mpr ht.2) ht.1 (show (0 : ℝ) ≤ 1 by norm_num) hR.le
    (show 1 - t + t = 1 by ring)
  simp only [Real.one_rpow, one_mul, mul_one] at ham
  have he : (u * B / (v * A)) ^ t * (u ^ (1 - t) * v ^ t) =
      u * (B / A) ^ t := by
    rw [Real.div_rpow (mul_pos hu hB).le (mul_pos hv hA).le,
      Real.mul_rpow hu.le hB.le, Real.mul_rpow hv.le hA.le,
      Real.rpow_sub hu 1 t, Real.rpow_one, Real.div_rpow hB.le hA.le]
    field_simp
  rw [← he]
  exact mul_le_mul_of_nonneg_right ham
    (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hv.le _))

theorem mass_geometric_factorization {A B t : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A * (B / A) ^ t = A ^ (1 - t) * B ^ t := by
  rw [Real.div_rpow hB.le hA.le, Real.rpow_sub hA 1 t, Real.rpow_one]
  ring

/-- The actual interval mass is the extended integral over its open interior. -/
theorem ofReal_mass_eq_lintegral_Ioo (f : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (mass f a b) = ∫⁻ x in Ioo a b, ENNReal.ofReal (f x) := by
  rw [mass, intervalIntegral.integral_of_le hab,
    ofReal_integral_eq_lintegral_ofReal hf.1 (Filter.Eventually.of_forall hfn)]
  exact (setLIntegral_congr Ioo_ae_eq_Ioc).symm

/-- Multiplication by a nonnegative constant under the actual open-interval integral. -/
theorem lintegral_Ioo_mul_ofReal (f : ℝ → ℝ) {a b k : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hk : 0 ≤ k) :
    (∫⁻ x in Ioo a b, ENNReal.ofReal (f x * k)) =
      ENNReal.ofReal (mass f a b * k) := by
  simp_rw [mul_comm (f _) k, ENNReal.ofReal_mul hk]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_mass_eq_lintegral_Ioo f hab hf hfn,
    ← ENNReal.ofReal_mul hk, mul_comm k]

/-- The actual transport proves the interval form of the multiplicative
integral inequality. The majorant hypothesis is the one supplied by the
lower-dimensional convex-volume inequality on actual sections. -/
theorem multiplicative_integral_bound (f : ℝ → ℝ) (a b : ℝ)
    (g : ℝ → ℝ) (c d t : ℝ) (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x)
    (hgc : ContinuousOn g (Ioo c d)) (ht : t ∈ Ioo 0 1)
    (H : ℝ → ℝ≥0∞)
    (hH : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
      ENNReal.ofReal (f x ^ (1 - t) * g y ^ t) ≤ H ((1 - t) * x + t * y)) :
    ENNReal.ofReal (mass f a b ^ (1 - t) * mass g c d ^ t) ≤
      ∫⁻ u in Ioo ((1 - t) * a + t * c) ((1 - t) * b + t * d), H u := by
  have hA := mass_pos f a b hab hf hfn hfp
  have hB := mass_pos g c d hcd hg hgn hgp
  rw [lintegral_interpolatedFunction f a b g c d t
    hab hf hfn hfp hfc hcd hg hgn hgp hgc ht]
  calc
    _ = ∫⁻ x in Ioo a b, ENNReal.ofReal (f x * (mass g c d / mass f a b) ^ t) := by
      rw [lintegral_Ioo_mul_ofReal f hab.le hf hfn
        (Real.rpow_nonneg (div_pos hB hA).le t), mass_geometric_factorization hA hB]
    _ ≤ _ := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro x hx
      have hy := matchingFunction_mapsTo_Ioo f a b g c d
        hab hf hfn hfp hcd hg hgn hgp hx
      have hv := hgp _ hy
      have hJ : 0 ≤ 1 - t + t * (f x * mass g c d /
          (g (matchingFunction f a b g c d x) * mass f a b)) :=
        add_nonneg (sub_nonneg.mpr ht.2.le) (mul_nonneg ht.1.le
          (div_nonneg (mul_nonneg (hfn x) hB.le) (mul_nonneg hv.le hA.le)))
      calc
        _ ≤ ENNReal.ofReal ((1 - t + t * (f x * mass g c d /
              (g (matchingFunction f a b g c d x) * mass f a b))) *
            (f x ^ (1 - t) * g (matchingFunction f a b g c d x) ^ t)) :=
          ENNReal.ofReal_le_ofReal (weighted_jacobian_geometric (hfp x hx) hv hA hB
            ⟨ht.1.le, ht.2.le⟩)
        _ = _ := ENNReal.ofReal_mul hJ
        _ ≤ _ := by gcongr; exact hH x hx _ hy

/-- The same bound on the actual closed image interval; endpoints are null. -/
theorem multiplicative_integral_bound_Icc (f : ℝ → ℝ) (a b : ℝ)
    (g : ℝ → ℝ) (c d t : ℝ) (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x)
    (hgc : ContinuousOn g (Ioo c d)) (ht : t ∈ Ioo 0 1)
    (H : ℝ → ℝ≥0∞)
    (hH : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
      ENNReal.ofReal (f x ^ (1 - t) * g y ^ t) ≤ H ((1 - t) * x + t * y)) :
    ENNReal.ofReal (mass f a b ^ (1 - t) * mass g c d ^ t) ≤
      ∫⁻ u in Icc ((1 - t) * a + t * c) ((1 - t) * b + t * d), H u := by
  rw [← setLIntegral_congr Ioo_ae_eq_Icc]
  exact multiplicative_integral_bound f a b g c d t
    hab hf hfn hfp hfc hcd hg hgn hgp hgc ht H hH

/-- The real-valued integral bound, for a nonnegative integrable majorant. -/
theorem multiplicative_integral_bound_real (f : ℝ → ℝ) (a b : ℝ)
    (g : ℝ → ℝ) (c d t : ℝ) (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x)
    (hgc : ContinuousOn g (Ioo c d)) (ht : t ∈ Ioo 0 1)
    (H : ℝ → ℝ) (hHi : IntervalIntegrable H volume
      ((1 - t) * a + t * c) ((1 - t) * b + t * d))
    (hHn : ∀ x, 0 ≤ H x)
    (hH : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
      f x ^ (1 - t) * g y ^ t ≤ H ((1 - t) * x + t * y)) :
    mass f a b ^ (1 - t) * mass g c d ^ t ≤
      ∫ u in ((1 - t) * a + t * c)..((1 - t) * b + t * d), H u := by
  have hz : (1 - t) * a + t * c ≤ (1 - t) * b + t * d :=
    add_le_add (mul_le_mul_of_nonneg_left hab.le (sub_nonneg.mpr ht.2.le))
      (mul_le_mul_of_nonneg_left hcd.le ht.1.le)
  have hb := multiplicative_integral_bound f a b g c d t
    hab hf hfn hfp hfc hcd hg hgn hgp hgc ht (fun x => ENNReal.ofReal (H x))
    (fun x hx y hy => ENNReal.ofReal_le_ofReal (hH x hx y hy))
  rw [← ofReal_mass_eq_lintegral_Ioo H hz hHi hHn] at hb
  exact (ENNReal.ofReal_le_ofReal_iff
    (intervalIntegral.integral_nonneg hz (fun x _ => hHn x))).mp hb

end ArakelovGeometry.Analysis.IntervalDensityTransport

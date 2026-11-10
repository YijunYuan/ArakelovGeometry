/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.MeasurableComplexEmbedding
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Polarization under an isometric complex field embedding

These identities preserve the existing inner product and use Mathlib's
conjugate-first convention. Either orientation of a complex embedding is allowed.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry

variable {L : Type*} [RCLike L]

/-- An isometric field embedding commutes with conjugation. -/
theorem complexEmbedding_map_conj (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (x : L) : σ (starRingEnd L x) = starRingEnd ℂ (σ x) := by
  by_cases hx : x = 0
  · simp [hx]
  apply mul_left_cancel₀ ((map_ne_zero σ).mpr hx)
  calc
    σ x * σ (starRingEnd L x) = σ (x * starRingEnd L x) := (map_mul σ _ _).symm
    _ = σ ((algebraMap ℝ L ‖x‖) ^ 2) := congrArg σ (RCLike.mul_conj x)
    _ = (‖σ x‖ : ℂ) ^ 2 := by
      rw [map_pow, complexEmbedding_apply_ofReal σ hσ, hσ]
    _ = σ x * starRingEnd ℂ (σ x) := (Complex.mul_conj' _).symm

/-- The real part is independent of the orientation of an isometric embedding. -/
theorem complexEmbedding_re (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : L) :
    (σ x).re = RCLike.re x := by
  have h := congrArg (fun z => (σ z).re) (RCLike.add_conj x)
  rw [map_add, complexEmbedding_map_conj σ hσ, map_mul, map_ofNat,
    show σ (RCLike.ofReal (RCLike.re x)) = (RCLike.re x : ℂ) from
    complexEmbedding_apply_ofReal σ hσ _] at h
  norm_num at h
  linarith

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace L V]

/-- Real polarization of the actual inner product in either complex orientation. -/
theorem complexEmbedding_inner_re (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (x y : V) :
    (σ (inner L x y)).re = (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) / 4 := by
  rw [complexEmbedding_re σ hσ]
  simpa only [pow_two] using re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four x y

/-- Imaginary polarization uses a completed scalar mapping to the usual `I`.
The signs correspond to conjugate-first inner products. -/
theorem complexEmbedding_inner_im (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (c : L) (hc : σ c = Complex.I) (x y : V) :
    (σ (inner L x y)).im = (‖x - c • y‖ ^ 2 - ‖x + c • y‖ ^ 2) / 4 := by
  have h := complexEmbedding_inner_re σ hσ x (c • y)
  rw [inner_smul_right, map_mul, hc, Complex.mul_re] at h
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at h
  linarith

/-- The finite Gram expansion commutes with the actual complex field embedding. -/
theorem complexEmbedding_inner_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (a : ι → L) (b : κ → L) (x : ι → V) (y : κ → V) :
    σ (inner L (∑ i, a i • x i) (∑ j, b j • y j)) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (a i)) * σ (inner L (x i) (y j)) * σ (b j) := by
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    map_sum, map_mul, complexEmbedding_map_conj σ hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Hermitian Gram quadratic form is exactly the squared existing norm. -/
theorem complexEmbedding_norm_sum_sq {ι : Type*} [Fintype ι]
    (σ : L →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (a : ι → L) (x : ι → V) :
    ‖∑ i, a i • x i‖ ^ 2 =
      (∑ i, ∑ j, starRingEnd ℂ (σ (a i)) * σ (inner L (x i) (x j)) * σ (a j)).re := by
  rw [← complexEmbedding_inner_sum σ hσ, inner_self_eq_norm_sq_to_K, map_pow]
  rw [show σ (RCLike.ofReal ‖∑ i, a i • x i‖) = (‖∑ i, a i • x i‖ : ℂ) from
    complexEmbedding_apply_ofReal σ hσ _]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

end ArakelovGeometry

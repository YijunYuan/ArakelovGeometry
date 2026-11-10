/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.JohnNorm

/-!
# Countable strict ellipsoid approximations

Rational real and imaginary coordinates give a countable dense family of
matrices over a real or complex scalar field. Approximating a slightly enlarged
John coordinate map gives positive definite Gram matrices with strict margins.
-/

open Matrix
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

noncomputable section

namespace ArakelovGeometry

variable (L : Type*) [RCLike L]

/-- The same rational pair parametrizes real rational and complex Gaussian
rational entries; the imaginary part vanishes over the real field. -/
def rationalEntry (q : ℚ × ℚ) : L := (q.1 : L) + (q.2 : L) * RCLike.I

/-- Rational pairs are dense over either real or complex scalars. -/
theorem denseRange_rationalEntry : DenseRange (rationalEntry L) := by
  let g : ℝ × ℝ → L := fun x => (x.1 : L) + (x.2 : L) * RCLike.I
  have hg : Function.Surjective g := fun z =>
    ⟨(RCLike.re z, RCLike.im z), RCLike.re_add_im z⟩
  have hc : Continuous g :=
    (RCLike.continuous_ofReal.comp continuous_fst).add
      ((RCLike.continuous_ofReal.comp continuous_snd).mul_const _)
  convert hg.denseRange.comp (Rat.denseRange_cast.prodMap Rat.denseRange_cast) hc using 1
  ext q
  simp only [Function.comp_def, Prod.map, g, rationalEntry, RCLike.ofReal_ratCast]

variable {n : Type*}

/-- Matrices from a countable set of rational coordinate pairs. -/
def rationalMatrix (Q : Matrix n n (ℚ × ℚ)) : Matrix n n L :=
  Q.map (rationalEntry L)

theorem denseRange_rationalMatrix : DenseRange (rationalMatrix (n := n) L) := by
  exact DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => denseRange_rationalEntry L))

variable {L} [Fintype n] [DecidableEq n]

/-- The rational matrix operators remain dense in the actual operator norm. -/
theorem denseRange_rationalMatrix_operator :
    DenseRange (fun Q : Matrix n n (ℚ × ℚ) =>
      (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) (rationalMatrix L Q)) := by
  let e := LinearEquiv.toContinuousLinearEquiv
    (Matrix.toEuclideanCLM (𝕜 := L) (n := n)).toAlgEquiv.toLinearEquiv
  exact e.surjective.denseRange.comp (denseRange_rationalMatrix L) e.continuous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace L E]

/-- Density also holds after pulling the coordinate operators back to the
original normed space. -/
theorem denseRange_rationalMatrix_comp (e : E ≃L[L] EuclideanSpace L n) :
    DenseRange (fun Q : Matrix n n (ℚ × ℚ) =>
      ((Matrix.toEuclideanCLM (𝕜 := L) (n := n))
        (rationalMatrix L Q)).comp e.toContinuousLinearMap) := by
  let a := e.symm.arrowCongr (ContinuousLinearEquiv.refl L (EuclideanSpace L n))
  exact a.surjective.denseRange.comp denseRange_rationalMatrix_operator a.continuous

/-- A rational matrix factor gives the dimension-sharp ellipsoid inequalities
with a positive rational margin. The original norm and coordinates are fixed;
the statement includes the empty coordinate space. -/
theorem exists_strict_rational_coordinates (e : E ≃L[L] EuclideanSpace L n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Q : Matrix n n (ℚ × ℚ)) (δ : ℚ), 0 < δ ∧ ∀ x : E,
      (1 + (δ : ℝ)) * ‖x‖ ^ 2 ≤
        ‖(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) (rationalMatrix L Q) (e x)‖ ^ 2 ∧
      ‖(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) (rationalMatrix L Q) (e x)‖ ^ 2 ≤
        (Fintype.card n + ε - (δ : ℝ)) * ‖x‖ ^ 2 := by
  obtain ⟨f, hf⟩ := exists_john_coordinates e
  let r := Real.sqrt (Fintype.card n)
  let a := Real.sqrt (Fintype.card n + ε)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hra : r < a := Real.sqrt_lt_sqrt (Nat.cast_nonneg _) (by linarith)
  have ha : a ^ 2 = Fintype.card n + ε := Real.sq_sqrt (by positivity)
  let t := (a - r) / (2 * (2 * r + 1))
  have ht : 0 < t := div_pos (sub_pos.mpr hra) (by positivity)
  have hteq : t * (2 * (2 * r + 1)) = a - r := div_mul_cancel₀ _ (by positivity)
  let c := 1 + 2 * t
  let b := c * r + t
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hba : b < a := by dsimp [b, c]; nlinarith
  have hlow : 0 < (1 + t) ^ 2 - 1 := by nlinarith
  have hupp : 0 < Fintype.card n + ε - b ^ 2 := by nlinarith
  obtain ⟨δ, hδ, hδlim⟩ := exists_rat_btwn (lt_min hlow hupp)
  have hδlow : 1 + (δ : ℝ) ≤ (1 + t) ^ 2 := by
    have := (lt_min_iff.mp hδlim).1
    linarith
  have hδupp : b ^ 2 ≤ Fintype.card n + ε - (δ : ℝ) := by
    have := (lt_min_iff.mp hδlim).2
    linarith
  let F : E →L[L] EuclideanSpace L n := (c : L) • f.toContinuousLinearMap
  obtain ⟨Q, hQ⟩ := (denseRange_rationalMatrix_comp e).exists_dist_lt F ht
  let T := ((Matrix.toEuclideanCLM (𝕜 := L) (n := n))
    (rationalMatrix L Q)).comp e.toContinuousLinearMap
  have hFT : ‖F - T‖ ≤ t := by simpa only [dist_eq_norm] using hQ.le
  refine ⟨Q, δ, by exact_mod_cast hδ, fun x => ?_⟩
  have herr : ‖F x - T x‖ ≤ t * ‖x‖ :=
    ((F - T).le_opNorm x).trans (mul_le_mul_of_nonneg_right hFT (norm_nonneg x))
  have hFx : ‖F x‖ = c * ‖f x‖ := by
    simp only [F, _root_.smul_apply, ContinuousLinearEquiv.coe_coe,
      norm_smul, RCLike.norm_of_nonneg hc]
  have hlo : (1 + t) * ‖x‖ ≤ ‖T x‖ := by
    have hsub := (norm_sub_norm_le (F x) (T x)).trans herr
    have hfx := mul_le_mul_of_nonneg_left (hf x).1 hc
    rw [hFx] at hsub
    dsimp [c] at hsub hfx
    nlinarith
  have hup : ‖T x‖ ≤ b * ‖x‖ := by
    have hsub := norm_sub_norm_le (T x) (F x)
    rw [norm_sub_rev, hFx] at hsub
    have hfx := mul_le_mul_of_nonneg_left (hf x).2 hc
    change c * ‖f x‖ ≤ c * (r * ‖x‖) at hfx
    dsimp [b]
    nlinarith
  constructor
  · calc
      (1 + (δ : ℝ)) * ‖x‖ ^ 2 ≤ (1 + t) ^ 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hδlow (sq_nonneg _)
      _ = ((1 + t) * ‖x‖) ^ 2 := (mul_pow _ _ _).symm
      _ ≤ ‖T x‖ ^ 2 := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hlo
  · calc
      ‖T x‖ ^ 2 ≤ (b * ‖x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hup
      _ = b ^ 2 * ‖x‖ ^ 2 := mul_pow _ _ _
      _ ≤ (Fintype.card n + ε - (δ : ℝ)) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hδupp (sq_nonneg _)

/-- The actual Gram matrix of a rational coordinate operator. -/
def rationalGram (Q : Matrix n n (ℚ × ℚ)) : Matrix n n L :=
  (rationalMatrix L Q).conjTranspose * rationalMatrix L Q

/-- Quadratic evaluation of the Gram matrix is exactly the squared operator norm
evaluation, with Mathlib's conjugate-first inner-product convention. -/
theorem rationalGram_quadratic (Q : Matrix n n (ℚ × ℚ)) (z : EuclideanSpace L n) :
    RCLike.re (inner L z ((Matrix.toEuclideanCLM (𝕜 := L) (n := n))
      (rationalGram (L := L) Q) z)) =
        ‖(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) (rationalMatrix L Q) z‖ ^ 2 := by
  rw [rationalGram, map_mul, ← Matrix.star_eq_conjTranspose, map_star,
    mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← norm_sq_eq_re_inner]

omit [DecidableEq n] in
theorem rationalGram_posSemidef (Q : Matrix n n (ℚ × ℚ)) :
    (rationalGram (L := L) Q).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- A positive strict lower bound forces the Gram matrix to be positive definite. -/
theorem rationalGram_posDef_of_lower_bound (e : E ≃L[L] EuclideanSpace L n)
    (Q : Matrix n n (ℚ × ℚ)) {c : ℝ} (hc : 0 < c)
    (hQ : ∀ x : E, c * ‖x‖ ^ 2 ≤
      ‖(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) (rationalMatrix L Q) (e x)‖ ^ 2) :
    (rationalGram (L := L) Q).PosDef := by
  let T := ((Matrix.toEuclideanCLM (𝕜 := L) (n := n))
    (rationalMatrix L Q)).comp e.toContinuousLinearMap
  have hT : Function.Injective T := (injective_iff_map_eq_zero T).mpr (by
    intro x hx
    have h := hQ x
    change c * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 at h
    rw [hx, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    have hsq : ‖x‖ ^ 2 ≤ 0 := le_of_mul_le_mul_left (by simpa using h) hc
    have hn : ‖x‖ = 0 := sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
    exact norm_eq_zero.mp hn)
  apply Matrix.PosDef.conjTranspose_mul_self
  intro x y hxy
  have h : T (e.symm (WithLp.toLp 2 x)) = T (e.symm (WithLp.toLp 2 y)) := by
    simp only [T, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.apply_symm_apply, Matrix.toEuclideanCLM_toLp, hxy]
  exact WithLp.toLp_injective 2 (e.symm.injective (hT h))

/-- Strict ellipsoid approximation by an explicit countable family of actual
positive definite Gram matrices. -/
theorem exists_strict_rational_ellipsoid (e : E ≃L[L] EuclideanSpace L n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Q : Matrix n n (ℚ × ℚ)) (δ : ℚ),
      0 < δ ∧ (rationalGram (L := L) Q).PosDef ∧ ∀ x : E,
      (1 + (δ : ℝ)) * ‖x‖ ^ 2 ≤
        RCLike.re (inner L (e x) ((Matrix.toEuclideanCLM (𝕜 := L) (n := n))
          (rationalGram (L := L) Q) (e x))) ∧
      RCLike.re (inner L (e x) ((Matrix.toEuclideanCLM (𝕜 := L) (n := n))
        (rationalGram (L := L) Q) (e x))) ≤
          (Fintype.card n + ε - (δ : ℝ)) * ‖x‖ ^ 2 := by
  obtain ⟨Q, δ, hδ, hQ⟩ := exists_strict_rational_coordinates e hε
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  refine ⟨Q, δ, hδ, rationalGram_posDef_of_lower_bound e Q (by positivity)
    (fun x => (hQ x).1), fun x => ?_⟩
  simpa only [rationalGram_quadratic] using hQ x

omit [DecidableEq n] in
theorem countable_range_rationalGram :
    Set.Countable (Set.range (rationalGram (L := L) (n := n))) := by
  let : Countable (Matrix n n (ℚ × ℚ)) :=
    show Countable (n → n → ℚ × ℚ) from inferInstance
  exact Set.countable_range _

omit [DecidableEq n] in
/-- Over the real field every Gram entry is rational. -/
theorem rationalGram_real_apply (Q : Matrix n n (ℚ × ℚ)) (i j : n) :
    rationalGram (L := ℝ) Q i j =
      ((∑ k, (Q k i).1 * (Q k j).1 : ℚ) : ℝ) := by
  simp [rationalGram, rationalMatrix, rationalEntry, Matrix.mul_apply]

omit [DecidableEq n] in
/-- Over the complex field the actual Hermitian Gram entries are Gaussian
rational, with an explicit common rational-pair parametrization. -/
theorem rationalGram_complex_apply (Q : Matrix n n (ℚ × ℚ)) (i j : n) :
    rationalGram (L := ℂ) Q i j =
      ((∑ k, ((Q k i).1 * (Q k j).1 + (Q k i).2 * (Q k j).2) : ℚ) : ℂ) +
        ((∑ k, ((Q k i).1 * (Q k j).2 - (Q k i).2 * (Q k j).1) : ℚ) : ℂ) *
          Complex.I := by
  apply Complex.ext
  · simp [rationalGram, rationalMatrix, rationalEntry, Matrix.mul_apply,
      Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
  · simp [rationalGram, rationalMatrix, rationalEntry, Matrix.mul_apply,
      Complex.mul_re, Complex.mul_im, sub_eq_add_neg, Finset.sum_add_distrib]

end ArakelovGeometry

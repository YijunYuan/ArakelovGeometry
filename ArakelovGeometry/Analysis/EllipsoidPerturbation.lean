/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.MaximalEllipsoid
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Perturbations in the contact-cone proof

Strict inward motion at the boundary of a compact subset of the Euclidean ball
persists uniformly for small positive parameters. Positive trace yields strict
determinant growth through the actual determinant polynomial.
-/

open Matrix
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

noncomputable section

namespace ArakelovGeometry

variable {L E : Type*} [RCLike L] [NormedAddCommGroup E] [InnerProductSpace L E]

/-- The exact quadratic expansion for a real perturbation in either scalar field. -/
theorem norm_add_real_smul_sq (T : E →L[L] E) (t : ℝ) (x : E) :
    ‖x + (algebraMap ℝ L t) • T x‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * t * RCLike.re (inner L x (T x)) + t ^ 2 * ‖T x‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := L), inner_smul_right, norm_smul, RCLike.algebraMap_eq_ofReal,
    RCLike.re_ofReal_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
  ring

/-- Strict inward motion at every unit contact is uniform on a compact subset
of the Euclidean unit ball. No uniform margin is assumed in the hypotheses. -/
theorem exists_uniform_inward_perturbation (T : E →L[L] E) {D : Set E}
    (hD : IsCompact D) (hball : ∀ x ∈ D, ‖x‖ ≤ 1)
    (hin : ∀ x ∈ D, ‖x‖ = 1 → RCLike.re (inner L x (T x)) < 0) :
    ∃ ε > 0, ∀ t : ℝ, 0 ≤ t → t < ε → ∀ x ∈ D,
      ‖x + (algebraMap ℝ L t) • T x‖ ≤ 1 := by
  let W : Set (ℝ × E) := {p | ‖p.2‖ ^ 2 +
      2 * p.1 * RCLike.re (inner L p.2 (T p.2)) + p.1 ^ 2 * ‖T p.2‖ ^ 2 < 1} ∪
    {p | 2 * RCLike.re (inner L p.2 (T p.2)) + p.1 * ‖T p.2‖ ^ 2 < 0}
  have hq : Continuous (fun p : ℝ × E => RCLike.re (inner L p.2 (T p.2))) :=
    RCLike.continuous_re.comp (continuous_snd.inner (T.continuous.comp continuous_snd))
  have hW : IsOpen W := by
    apply IsOpen.union
    · exact isOpen_lt (((continuous_snd.norm.pow 2).add
        ((continuous_const.mul continuous_fst).mul hq)).add
        ((continuous_fst.pow 2).mul ((T.continuous.comp continuous_snd).norm.pow 2)))
        continuous_const
    · exact isOpen_lt ((continuous_const.mul hq).add
        (continuous_fst.mul ((T.continuous.comp continuous_snd).norm.pow 2))) continuous_const
  have hzero : ({0} : Set ℝ) ×ˢ D ⊆ W := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have ht0 : t = 0 := ht
    subst t
    by_cases hnorm : ‖x‖ = 1
    · right
      simp only [Set.mem_ofPred_eq, zero_mul, add_zero]
      linarith [hin x hx hnorm]
    · left
      have hnlt : ‖x‖ < 1 := lt_of_le_of_ne (hball x hx) hnorm
      simp only [Set.mem_ofPred_eq, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0),
        add_zero]
      nlinarith [norm_nonneg x]
  obtain ⟨U, V, hU, _, h0U, hDV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hD hW hzero
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU 0 (h0U (by simp))
  refine ⟨ε, hε, fun t ht htε x hx => ?_⟩
  have htU : t ∈ U := hεU (by simpa only [Metric.mem_ball, dist_zero_right,
    Real.norm_eq_abs, abs_of_nonneg ht] using htε)
  have htx : (t, x) ∈ W := hUV ⟨htU, hDV hx⟩
  have hn : ‖x‖ ^ 2 ≤ 1 := by nlinarith [hball x hx, norm_nonneg x]
  have hsq : ‖x + (algebraMap ℝ L t) • T x‖ ^ 2 ≤ 1 := by
    rw [norm_add_real_smul_sq]
    rcases htx with h | h
    · exact h.le
    · have hmul := mul_nonpos_of_nonneg_of_nonpos ht h.le
      nlinarith
  nlinarith [norm_nonneg (x + (algebraMap ℝ L t) • T x)]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of a Hermitian matrix is real in the original scalar field. -/
theorem hermitian_matrix_inner_im_zero {H : Matrix n n L} (hH : H.IsHermitian)
    (x : EuclideanSpace L n) :
    RCLike.im (inner L x ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) H x)) = 0 := by
  have hT := hH.isSelfAdjoint.map (Matrix.toEuclideanCLM (𝕜 := L) (n := n))
  rw [← RCLike.conj_eq_iff_im, inner_conj_symm, hT.isSymmetric.apply_clm]

/-- Positive real quadratic forms on all nonzero Euclidean vectors give an
actual positive definite Hermitian matrix. -/
theorem posDef_of_re_inner_pos {H : Matrix n n L} (hH : H.IsHermitian)
    (hpos : ∀ x : EuclideanSpace L n, x ≠ 0 →
      0 < RCLike.re (inner L x ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) H x))) :
    H.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hH
  intro x hx
  let u : EuclideanSpace L n := WithLp.toLp 2 x
  have hu : u ≠ 0 := by simpa only [u, ne_eq, WithLp.toLp_eq_zero] using hx
  have hreal := hermitian_matrix_inner_im_zero hH u
  have hp := hpos u hu
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM] at hreal hp
  exact RCLike.pos_iff.mpr ⟨by simpa only [dotProduct_comm] using hp,
    by simpa only [dotProduct_comm] using hreal⟩

/-- Evaluation of a real affine matrix perturbation uses the actual Euclidean action. -/
theorem toEuclideanCLM_one_add_real_smul (H : Matrix n n L) (t : ℝ)
    (x : EuclideanSpace L n) :
    (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) (1 + (algebraMap ℝ L t) • H) x =
      x + (algebraMap ℝ L t) • (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) H x := by
  let e := (Matrix.toEuclideanCLM (𝕜 := L) (n := n)).toAlgEquiv.toLinearMap
  have hone : e 1 = 1 := map_one (Matrix.toEuclideanCLM (𝕜 := L) (n := n))
  change (e (1 + (algebraMap ℝ L t) • H)) x = _
  rw [map_add, map_smul, hone]
  rfl

/-- Sufficiently small self-adjoint perturbations of the identity remain positive
definite, with a bound in the actual Euclidean operator norm. -/
theorem posDef_one_add_real_smul_of_small {H : Matrix n n L} (hH : H.IsHermitian)
    {t : ℝ} (ht : 0 ≤ t)
    (hsmall : t * ‖(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) H‖ < 1) :
    (1 + (algebraMap ℝ L t) • H).PosDef := by
  have hself : IsSelfAdjoint (algebraMap ℝ L t) := by simp [isSelfAdjoint_iff]
  apply posDef_of_re_inner_pos (Matrix.isHermitian_one.add (hH.smul hself))
  intro x hx
  let T := (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) H
  have hbound : |RCLike.re (inner L x (T x))| ≤ ‖T‖ * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖inner L x (T x)‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg _)
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_left (abs_le.mp hbound).1 ht
  have hsq : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hgap : 0 < (1 - t * ‖T‖) * ‖x‖ ^ 2 := mul_pos (sub_pos.mpr hsmall) hsq
  rw [toEuclideanCLM_one_add_real_smul, inner_add_right, inner_smul_right,
    map_add, inner_self_eq_norm_sq_to_K, ← map_pow, RCLike.ofReal_re,
    RCLike.algebraMap_eq_ofReal, RCLike.re_ofReal_mul]
  change 0 < ‖x‖ ^ 2 + t * RCLike.re (inner L x (T x))
  nlinarith

/-- Positive real trace gives actual strict determinant growth for all
sufficiently small positive real perturbations. -/
theorem exists_det_growth_real_perturbation (H : Matrix n n L)
    (htrace : 0 < RCLike.re H.trace) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
      1 < RCLike.re (1 + (algebraMap ℝ L t) • H).det := by
  let p : Polynomial L :=
    (1 + (Polynomial.X : Polynomial L) • H.map (Polynomial.C : L →+* Polynomial L)).det.divX.divX
  let g : ℝ → ℝ := fun t => RCLike.re H.trace + t * RCLike.re (p.eval (algebraMap ℝ L t))
  have hg : Continuous g := by
    exact continuous_const.add (continuous_id.mul
      (RCLike.continuous_re.comp (p.continuous.comp RCLike.continuous_ofReal)))
  have h0 : 0 ∈ {t | 0 < g t} := by simpa [g] using htrace
  obtain ⟨ε, hε, hεg⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt continuous_const hg).mem_nhds h0)
  refine ⟨ε, hε, fun t ht htε => ?_⟩
  have hgt : 0 < g t := hεg (by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht] using htε)
  have hprod := mul_pos ht hgt
  change 0 < t * (RCLike.re H.trace + t * RCLike.re (p.eval (algebraMap ℝ L t))) at hprod
  rw [Matrix.det_one_add_smul]
  simp only [map_add, RCLike.one_re, RCLike.algebraMap_eq_ofReal,
    RCLike.re_mul_ofReal, ← map_pow] at *
  change 1 < 1 + RCLike.re H.trace * t + RCLike.re (p.eval (RCLike.ofReal t)) * t ^ 2
  nlinarith

/-- A Hermitian direction with positive trace and strict inward motion at every
unit contact produces a genuine larger positive ellipsoid on the compact polar. -/
theorem exists_larger_ellipsoid_of_inward_direction {D : Set (EuclideanSpace L n)}
    (hD : IsCompact D) (hball : ∀ x ∈ D, ‖x‖ ≤ 1)
    (H : Matrix n n L) (hH : H.IsHermitian) (htrace : 0 < RCLike.re H.trace)
    (hin : ∀ x ∈ D, ‖x‖ = 1 →
      RCLike.re (inner L x ((Matrix.toEuclideanCLM (𝕜 := L) (n := n)) H x)) < 0) :
    ∃ A : Matrix n n L, A.PosDef ∧ 1 < RCLike.re A.det ∧
      ∀ x ∈ D, ‖(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A x‖ ≤ 1 := by
  let T := (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) H
  obtain ⟨ε₁, hε₁, hinward⟩ := exists_uniform_inward_perturbation T hD hball hin
  obtain ⟨ε₂, hε₂, hdet⟩ := exists_det_growth_real_perturbation H htrace
  have hnorm : 0 < ‖T‖ + 1 := by positivity
  have hmin : 0 < min ε₁ (min ε₂ (1 / (‖T‖ + 1))) :=
    lt_min hε₁ (lt_min hε₂ (one_div_pos.mpr hnorm))
  obtain ⟨t, ht, htm⟩ := exists_between hmin
  have ht₁ := htm.trans_le (min_le_left _ _)
  have ht₂ := (htm.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have htp := (htm.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hsmall : t * ‖T‖ < 1 := by
    have hb := (lt_div_iff₀ hnorm).mp htp
    nlinarith
  refine ⟨1 + (algebraMap ℝ L t) • H, posDef_one_add_real_smul_of_small hH ht.le hsmall,
    hdet t ht ht₂, fun x hx => ?_⟩
  rw [toEuclideanCLM_one_add_real_smul]
  exact hinward t ht.le ht₁ x hx

end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.HermitianScalarExtension

/-!
# A real norm does not determine a Hermitian extension

The positive Hermitian matrix with rows `(1, I/2)` and `(-I/2, 1)`
defines a norm on the complex plane which restricts to the Euclidean norm on
the real plane, but differs from its canonical Hermitian complexification.
-/

noncomputable section

namespace ArakelovGeometry

/-- A Cholesky map for the explicit nonstandard Hermitian form. -/
def realRestrictionCounterexampleMap :
    EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun z := WithLp.toLp 2 ![z 0 + Complex.I / 2 * z 1, (Real.sqrt 3 : ℂ) / 2 * z 1]
  map_add' z t := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a z := by
    ext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

/-- The Cholesky map is injective, so its pullback form is positive definite. -/
theorem realRestrictionCounterexampleMap_injective :
    Function.Injective realRestrictionCounterexampleMap := by
  intro z t h
  have h1 := congrArg (fun y : EuclideanSpace ℂ (Fin 2) ↦ y 1) h
  change (Real.sqrt 3 : ℂ) / 2 * z 1 = (Real.sqrt 3 : ℂ) / 2 * t 1 at h1
  have hs : (Real.sqrt 3 : ℂ) / 2 ≠ 0 := by
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))
      (by norm_num)
  have hz1 := mul_left_cancel₀ hs h1
  have h0 := congrArg (fun y : EuclideanSpace ℂ (Fin 2) ↦ y 0) h
  change z 0 + Complex.I / 2 * z 1 = t 0 + Complex.I / 2 * t 1 at h0
  rw [hz1] at h0
  have hz0 := add_right_cancel h0
  ext i
  fin_cases i
  · exact hz0
  · exact hz1

/-- The positive definite Hermitian form of the counterexample. -/
@[instance_reducible]
def realRestrictionCounterexampleCore : InnerProductSpace.Core ℂ (EuclideanSpace ℂ (Fin 2)) where
  inner z t := inner ℂ (realRestrictionCounterexampleMap z) (realRestrictionCounterexampleMap t)
  conj_inner_symm _ _ := inner_conj_symm _ _
  re_inner_nonneg _ := inner_self_nonneg
  add_left z t u := by simp only [map_add, inner_add_left]
  smul_left z t a := by simp only [map_smul, inner_smul_left]
  definite z h := realRestrictionCounterexampleMap_injective
    ((inner_self_eq_zero.mp h).trans (map_zero _).symm)

/-- The norm of the counterexample, expressed as a separated seminorm
on the existing complex plane. -/
def realRestrictionCounterexampleSeminorm : Seminorm ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (normSeminorm ℂ (EuclideanSpace ℂ (Fin 2))).comp realRestrictionCounterexampleMap

theorem realRestrictionCounterexampleSeminorm_eq_zero_iff (z : EuclideanSpace ℂ (Fin 2)) :
    realRestrictionCounterexampleSeminorm z = 0 ↔ z = 0 := by
  change ‖realRestrictionCounterexampleMap z‖ = 0 ↔ z = 0
  rw [norm_eq_zero]
  exact realRestrictionCounterexampleMap_injective.eq_iff' (map_zero _)

/-- The positive definite pairing induces exactly the counterexample norm. -/
theorem realRestrictionCounterexampleSeminorm_sq (z : EuclideanSpace ℂ (Fin 2)) :
    (realRestrictionCounterexampleSeminorm z) ^ 2 =
      (realRestrictionCounterexampleCore.inner z z).re :=
  norm_sq_eq_re_inner (𝕜 := ℂ) (realRestrictionCounterexampleMap z)

/-- The form has exactly the matrix with rows `(1, I/2)` and `(-I/2, 1)`
in the standard coordinate basis, with conjugate-first convention. -/
theorem realRestrictionCounterexampleCore_apply (z t : EuclideanSpace ℂ (Fin 2)) :
    realRestrictionCounterexampleCore.inner z t =
      starRingEnd ℂ (z 0) * t 0 + starRingEnd ℂ (z 1) * t 1 +
        Complex.I / 2 * (starRingEnd ℂ (z 0) * t 1 - starRingEnd ℂ (z 1) * t 0) := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  change inner ℂ (realRestrictionCounterexampleMap z) (realRestrictionCounterexampleMap t) = _
  simp only [PiLp.inner_apply, Fin.sum_univ_two, realRestrictionCounterexampleMap,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, RCLike.inner_apply, map_add, map_mul]
  norm_num [map_div₀, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofNat]
  ring_nf
  simp only [Complex.I_sq, hs]
  ring

/-- The exact quadratic form includes a nonzero imaginary cross term. -/
theorem realRestrictionCounterexampleSeminorm_sq_formula (z : EuclideanSpace ℂ (Fin 2)) :
    (realRestrictionCounterexampleSeminorm z) ^ 2 =
      ‖z 0‖ ^ 2 + ‖z 1‖ ^ 2 - (starRingEnd ℂ (z 0) * z 1).im := by
  rw [realRestrictionCounterexampleSeminorm_sq, realRestrictionCounterexampleCore_apply]
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.div_im,
    Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.sub_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

/-- On the original real plane the new norm is exactly Euclidean. -/
theorem realRestrictionCounterexampleSeminorm_on_real (x : EuclideanSpace ℝ (Fin 2)) :
    realRestrictionCounterexampleSeminorm
      (WithLp.toLp 2 (fun i ↦ (x i : ℂ))) = ‖x‖ := by
  apply (sq_eq_sq₀ (apply_nonneg _ _) (norm_nonneg _)).mp
  rw [realRestrictionCounterexampleSeminorm_sq_formula, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_two]
  simp [Complex.conj_ofReal]

/-- The nonstandard norm equals one at the vector `(1, I)`. -/
theorem realRestrictionCounterexampleSeminorm_one_I :
    realRestrictionCounterexampleSeminorm (WithLp.toLp 2 ![1, Complex.I]) = 1 := by
  apply (sq_eq_sq₀ (apply_nonneg _ _) zero_le_one).mp
  rw [realRestrictionCounterexampleSeminorm_sq_formula]
  norm_num

/-- The standard Euclidean norm of the same vector is `sqrt 2`. -/
theorem euclideanPlane_norm_one_I :
    ‖(WithLp.toLp 2 ![1, Complex.I] : EuclideanSpace ℂ (Fin 2))‖ = Real.sqrt 2 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The two norms on the complex plane are distinct despite having the
same restriction to every real vector. -/
theorem realRestrictionCounterexampleSeminorm_ne_euclidean :
    realRestrictionCounterexampleSeminorm ≠ normSeminorm ℂ (EuclideanSpace ℂ (Fin 2)) := by
  intro h
  have hh := congrArg (fun p : Seminorm ℂ (EuclideanSpace ℂ (Fin 2)) ↦
    (p (WithLp.toLp 2 ![1, Complex.I])) ^ 2) h
  change (realRestrictionCounterexampleSeminorm (WithLp.toLp 2 ![1, Complex.I])) ^ 2 =
    ‖(WithLp.toLp 2 ![1, Complex.I] : EuclideanSpace ℂ (Fin 2))‖ ^ 2 at hh
  rw [realRestrictionCounterexampleSeminorm_one_I, euclideanPlane_norm_one_I,
    Real.sq_sqrt (by norm_num)] at hh
  norm_num at hh

/-- Unlike its norm, the candidate pairing does not restrict to the
original real inner product: its value on the coordinate vectors is `I/2`. -/
theorem realRestrictionCounterexampleCore_basis_pairing :
    realRestrictionCounterexampleCore.inner
      (WithLp.toLp 2 ![1, 0]) (WithLp.toLp 2 ![0, 1]) = Complex.I / 2 := by
  rw [realRestrictionCounterexampleCore_apply]
  simp

/-- A concrete positive definite Hermitian norm which extends the real
Euclidean norm but is not its canonical Hermitian complexification. -/
theorem exists_distinct_hermitian_norm_with_real_euclidean_restriction :
    ∃ p : Seminorm ℂ (EuclideanSpace ℂ (Fin 2)),
      (∀ z, p z = 0 ↔ z = 0) ∧
      (∃ c : InnerProductSpace.Core ℂ (EuclideanSpace ℂ (Fin 2)),
        ∀ z, (p z) ^ 2 = (c.inner z z).re) ∧
      (∀ x : EuclideanSpace ℝ (Fin 2), p (WithLp.toLp 2 (fun i ↦ (x i : ℂ))) = ‖x‖) ∧
      p ≠ normSeminorm ℂ (EuclideanSpace ℂ (Fin 2)) :=
  ⟨realRestrictionCounterexampleSeminorm, realRestrictionCounterexampleSeminorm_eq_zero_iff,
    ⟨realRestrictionCounterexampleCore, realRestrictionCounterexampleSeminorm_sq⟩,
    realRestrictionCounterexampleSeminorm_on_real,
    realRestrictionCounterexampleSeminorm_ne_euclidean⟩

end ArakelovGeometry

end

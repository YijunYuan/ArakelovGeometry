/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NonpureNumberFieldMinkowskiObstructionFiniteArithmetic

/-! # Actual vector degrees of the nonpure rational plane -/

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

open AdelicStructure NormFamily

theorem rational_infinite_mass : S.v S.Ωinf = 1 := by
  have h := normalizedNumberFieldAdelicStructure_v_Ωinf (K := ℚ)
  erw [Module.finrank_self] at h
  simpa only [Nat.cast_one] using h

theorem rational_infinite_real_mass : S.v.real S.Ωinf = 1 := by
  rw [measureReal_def, rational_infinite_mass, ENNReal.toReal_one]

theorem primitive_integer_vector_ne_zero (x y : ℤ) (hxy : IsCoprime x y) :
    (![x, y] : Plane) ≠ 0 := by
  intro h
  have hx : x = 0 := by
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
    exact_mod_cast h0
  have hy : y = 0 := by
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply] at h1
    exact_mod_cast h1
  obtain ⟨b, c, hb⟩ := hxy
  simp only [hx, hy, mul_zero, add_zero] at hb
  exact zero_ne_one hb

open Classical in
theorem family_primitive_logNorm_profile (p : Nat.Primes) (a x y : ℤ)
    (hxy : IsCoprime x y) :
    (family p a).logNorm (![x, y] : Plane) =
      S.Ωinf.indicator (fun _ => Real.log (Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))) +
      ({primePoint p} : Set S.Ω).indicator
        (fun _ => if (p.val : ℤ) ∣ y - a * x then 0 else Real.log (p.val : ℝ) / 2) := by
  funext ω
  change Real.log ((family p a).norm ω (1 ⊗ₜ[ℚ] (![x, y] : Plane))) = _
  rw [family_norm_integer_primitive_profile p a ω x y hxy]
  by_cases hi : ω ∈ S.Ωinf
  · have he : ω ≠ primePoint p := fun he => hi (he ▸ primePoint_mem_fin p)
    simp [hi, he]
  · by_cases he : ω = primePoint p
    · subst ω
      by_cases hc : (p.val : ℤ) ∣ y - a * x <;>
        simp [hi, hc, Real.log_sqrt (by positivity : (0 : ℝ) ≤ p.val)]
    · simp [hi, he]

open Classical in
theorem family_primitive_integral_logNorm (p : Nat.Primes) (a x y : ℤ)
    (hxy : IsCoprime x y) :
    (∫ ω, (family p a).logNorm (![x, y] : Plane) ω ∂S.v) =
      Real.log (Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) +
      if (p.val : ℤ) ∣ y - a * x then 0 else Real.log (p.val : ℝ) / 2 := by
  let : DiscreteMeasurableSpace S.Ω := inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})
  have hinf : Integrable
      (S.Ωinf.indicator (fun _ => Real.log (Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)))) S.v :=
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr
      (integrableOn_const (by rw [rational_infinite_mass]; exact ENNReal.one_ne_top))
  have hfin : Integrable (({primePoint p} : Set S.Ω).indicator
      (fun _ => if (p.val : ℤ) ∣ y - a * x then 0 else Real.log (p.val : ℝ) / 2)) S.v :=
    (integrable_indicator_iff (measurableSet_singleton _)).mpr
      (integrableOn_const (by rw [rational_singleton_mass]; exact ENNReal.one_ne_top))
  rw [family_primitive_logNorm_profile p a x y hxy]
  change (∫ ω, S.Ωinf.indicator
      (fun _ : S.Ω => Real.log (Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2))) ω +
      ({primePoint p} : Set S.Ω).indicator
        (fun _ : S.Ω => if (p.val : ℤ) ∣ y - a * x then 0 else Real.log (p.val : ℝ) / 2) ω
      ∂S.v) = _
  rw [integral_add hinf hfin, integral_indicator_const _ S.measurableSet_Ωinf,
    integral_indicator_const _ (measurableSet_singleton _),
    rational_infinite_real_mass, rational_singleton_real_mass, one_smul, one_smul]

open Classical in
theorem bundle_primitive_vectorDegree (p : Nat.Primes) (a x y : ℤ)
    (hxy : IsCoprime x y) :
    (bundle p a).vectorDegree ⟨(![x, y] : Plane), primitive_integer_vector_ne_zero x y hxy⟩ =
      -Real.log (Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) -
      if (p.val : ℤ) ∣ y - a * x then 0 else Real.log (p.val : ℝ) / 2 := by
  rw [AdelicVectorBundle.vectorDegree, NormFamily.vectorDegree_eq_neg_integral]
  change -(∫ ω, (family p a).logNorm (![x, y] : Plane) ω ∂S.v) = _
  rw [family_primitive_integral_logNorm p a x y hxy]
  ring

theorem bundle_primitive_vectorDegree_le (p : Nat.Primes) (a x y : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) (hxy : IsCoprime x y) :
    (bundle p a).vectorDegree ⟨(![x, y] : Plane), primitive_integer_vector_ne_zero x y hxy⟩ ≤
      -Real.log (p.val : ℝ) / 2 := by
  classical
  rw [bundle_primitive_vectorDegree p a x y hxy]
  by_cases hc : (p.val : ℤ) ∣ y - a * x
  · simp only [hc, ite_true, sub_zero]
    have hroot := primitive_good_congruence_euclidean_bound p a x y ha hxy hc
    have hlog := Real.log_le_log (Real.sqrt_pos.mpr
      (by exact_mod_cast p.property.pos)) hroot
    rw [Real.log_sqrt (by positivity)] at hlog
    linarith
  · simp only [hc, ite_false]
    have hlog := Real.log_nonneg (primitive_one_le_euclidean x y hxy)
    linarith

theorem bundle_axis_zero_vectorDegree (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) :
    (bundle p a).vectorDegree
      ⟨(![1, 0] : Plane), by simpa only [Int.cast_one, Int.cast_zero] using
        primitive_integer_vector_ne_zero 1 0 isCoprime_one_left⟩ =
      -Real.log (p.val : ℝ) / 2 := by
  classical
  have hc : ¬ (p.val : ℤ) ∣ a := prime_not_dvd_root_minus_one p a ha
  simpa [hc, neg_div] using bundle_primitive_vectorDegree p a 1 0 isCoprime_one_left

theorem bundle_axis_one_vectorDegree (p : Nat.Primes) (a : ℤ) :
    (bundle p a).vectorDegree
      ⟨(![0, 1] : Plane), by simpa only [Int.cast_one, Int.cast_zero] using
        primitive_integer_vector_ne_zero 0 1 isCoprime_one_right⟩ =
      -Real.log (p.val : ℝ) / 2 := by
  classical
  have hc : ¬ (p.val : ℤ) ∣ (1 : ℤ) := by
    intro h
    exact p.property.not_dvd_one (by exact_mod_cast h)
  simpa [hc, neg_div] using bundle_primitive_vectorDegree p a 0 1 isCoprime_one_right

/-- A genuine reduced-fraction construction of a primitive integral representative. -/
theorem exists_primitive_integer_representative (v : Plane) (hv : v ≠ 0) :
    ∃ (c : ℚˣ) (x y : ℤ), IsCoprime x y ∧ v = (c : ℚ) • (![x, y] : Plane) := by
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      ext i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, h0, h1, Pi.zero_apply]
    refine ⟨Units.mk0 (v 0) h0, 1, 0, isCoprime_one_left, ?_⟩
    ext i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Pi.smul_apply, Units.val_mk0,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Int.cast_one, Int.cast_zero, smul_eq_mul, mul_one, mul_zero, h1]
  · let q := v 0 / v 1
    have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    refine ⟨Units.mk0 (v 1 / (q.den : ℚ)) (div_ne_zero h1 hd),
      q.num, (q.den : ℤ), q.isCoprime_num_den, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, Units.val_mk0, Matrix.cons_val_zero, smul_eq_mul]
      calc
        v 0 = (v 0 / v 1) * v 1 := (div_mul_cancel₀ _ h1).symm
        _ = q * v 1 := rfl
        _ = ((q.num : ℚ) / (q.den : ℚ)) * v 1 := by rw [Rat.num_div_den]
        _ = (v 1 / (q.den : ℚ)) * (q.num : ℚ) := by ring
    · simp only [Fin.mk_one, Pi.smul_apply, Units.val_mk0, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Int.cast_natCast, smul_eq_mul]
      exact (div_mul_cancel₀ _ hd).symm

theorem bundle_vectorDegree_le (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) (v : {x : Plane // x ≠ 0}) :
    (bundle p a).vectorDegree v ≤ -Real.log (p.val : ℝ) / 2 := by
  let : S.IsProper := normalizedNumberFieldAdelicStructure_isProper
  obtain ⟨c, x, y, hxy, hv⟩ := exists_primitive_integer_representative v.val v.property
  have he : (bundle p a).vectorDegree v =
      (bundle p a).vectorDegree
        ⟨(![x, y] : Plane), primitive_integer_vector_ne_zero x y hxy⟩ := by
    change (family p a).vectorDegree (family_coherent_and_dominated p a).2
      (family_isMeasurable p a) v =
      (family p a).vectorDegree (family_coherent_and_dominated p a).2
        (family_isMeasurable p a) ⟨(![x, y] : Plane), primitive_integer_vector_ne_zero x y hxy⟩
    have hv' : v = ⟨(c : ℚ) • (![x, y] : Plane),
        smul_ne_zero c.ne_zero (primitive_integer_vector_ne_zero x y hxy)⟩ := Subtype.ext hv
    rw [hv']
    exact (family p a).vectorDegree_smul_of_proper (family_coherent_and_dominated p a).2
      (family_isMeasurable p a) c
      ⟨(![x, y] : Plane), primitive_integer_vector_ne_zero x y hxy⟩
  rw [he]
  exact bundle_primitive_vectorDegree_le p a x y ha hxy

end ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

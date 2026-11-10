/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NonpureNumberFieldMinkowskiObstructionArithmetic
public import ArakelovGeometry.NumberTheory.NormalizedNumberFieldLocalDegree

/-! # Actual finite-place arithmetic for the nonpure rational plane -/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

open AdelicStructure ActualPrimeIndexing AdelicStructure.NormalizedNumberFieldPlaces NormFamily

theorem primeIdeal_mem_integer (p : Nat.Primes) (n : ℤ) :
    (n : 𝓞 ℚ) ∈ (primeIdeal p).asIdeal ↔ (p.val : ℤ) ∣ n := by
  have hg : Rat.HeightOneSpectrum.natGenerator (primeIdeal p) = p.val :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)
  rw [← Ideal.apply_mem_of_equiv_iff
    (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)),
    ← Rat.HeightOneSpectrum.span_natGenerator, hg]
  simp only [map_intCast, Int.cast_id, Ideal.mem_span_singleton]

theorem rational_normalizedPrimeValue_eq_finitePlace (p : Nat.Primes) (x : ℚ) :
    S.ϕ (primePoint p) x = (FinitePlace.mk (primeIdeal p)) x := by
  have h := normalizedPlaceValue_eq_finitePlace_rpow (FinitePlace.mk (primeIdeal p)) x
  have hd := rational_localDegree_one (A := DivisionRing.toRatAlgebra)
    (normalizedPlaceValue ⟨Quotient.mk' (FinitePlace.mk (primeIdeal p)).val,
      mk_finitePlace_ne_trivialPlace (FinitePlace.mk (primeIdeal p))⟩)
  simp only [hd, Nat.cast_one, inv_one, Real.rpow_one] at h
  exact h

theorem rational_primeValue_integer_le_one (p : Nat.Primes) (n : ℤ) :
    S.ϕ (primePoint p) (n : ℚ) ≤ 1 :=
  (primePoint_mem_fin p).apply_intCast_le_one
    (map_zero_le _ 1) (map_one _) (S.ϕ (primePoint p)).map_neg

theorem rational_primeValue_integer_lt_one_iff (p : Nat.Primes) (n : ℤ) :
    S.ϕ (primePoint p) (n : ℚ) < 1 ↔ (p.val : ℤ) ∣ n := by
  rw [rational_normalizedPrimeValue_eq_finitePlace]
  have hn := FinitePlace.norm_embedding_eq (FinitePlace.mk (primeIdeal p)) (n : ℚ)
  rw [FinitePlace.maximalIdeal_mk] at hn
  rw [← hn]
  have h := FinitePlace.norm_lt_one_iff_mem ℚ (primeIdeal p) (n : 𝓞 ℚ)
  simpa only [map_intCast, primeIdeal_mem_integer] using h

theorem rational_primeValue_integer_eq_one (p : Nat.Primes) (n : ℤ)
    (hn : ¬ (p.val : ℤ) ∣ n) : S.ϕ (primePoint p) (n : ℚ) = 1 := by
  apply le_antisymm (rational_primeValue_integer_le_one p n)
  exact le_of_not_gt (fun h => hn ((rational_primeValue_integer_lt_one_iff p n).mp h))

theorem primePoint_base (p : Nat.Primes) :
    (parameterMeasurableEquivNontrivialPlace.symm (primePoint p)).base = Sum.inl p := by
  obtain ⟨q, hq⟩ := normalizedPrimeParameter_exists_base_prime (primeIdeal p)
  have hval := normalizedPlaceValue_apply_base_prime (primePoint p) q hq
  have hlt : S.ϕ (primePoint p) (q.val : ℚ) < 1 := by
    change normalizedPlaceValue (primePoint p) (q.val : ℚ) < 1
    rw [hval]
    exact (inv_lt_one₀ (by exact_mod_cast q.property.pos)).mpr
      (by exact_mod_cast q.property.one_lt)
  have hd : p.val ∣ q.val := by
    have hi := (rational_primeValue_integer_lt_one_iff p (q.val : ℤ)).mp
      (by simpa only [Int.cast_natCast] using hlt)
    exact_mod_cast hi
  have he : q = p := Subtype.ext ((q.property.dvd_iff_eq p.property.ne_one).mp hd)
  subst q
  exact hq

theorem rational_primeValue_prime (p : Nat.Primes) :
    S.ϕ (primePoint p) (p.val : ℚ) = (p.val : ℝ)⁻¹ :=
  normalizedPlaceValue_apply_base_prime (primePoint p) p (primePoint_base p)

theorem rational_primeValue_integer_le_inv_of_dvd (p : Nat.Primes) (n : ℤ)
    (hn : (p.val : ℤ) ∣ n) :
    S.ϕ (primePoint p) (n : ℚ) ≤ (p.val : ℝ)⁻¹ := by
  obtain ⟨m, rfl⟩ := hn
  rw [Int.cast_mul, Int.cast_natCast, map_mul, rational_primeValue_prime]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (rational_primeValue_integer_le_one p m) (by positivity : 0 ≤ (p.val : ℝ)⁻¹)

theorem family_norm_prime_integer_bad (p : Nat.Primes) (a x y : ℤ)
    (hc : ¬ (p.val : ℤ) ∣ y - a * x) :
    (family p a).norm (primePoint p) (1 ⊗ₜ[ℚ] (![x, y] : Plane)) =
      Real.sqrt (p.val : ℝ) := by
  rw [family_norm_prime_rational]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hs : (y : ℚ) - (a : ℚ) * (x : ℚ) = ((y - a * x : ℤ) : ℚ) := by push_cast; rfl
  rw [hs, rational_primeValue_integer_eq_one p (y - a * x) hc, mul_one]
  apply max_eq_right
  exact (rational_primeValue_integer_le_one p x).trans
    (Real.one_le_sqrt.mpr (by exact_mod_cast p.property.one_le))

theorem family_norm_prime_integer_good (p : Nat.Primes) (a x y : ℤ)
    (hxy : IsCoprime x y) (hc : (p.val : ℤ) ∣ y - a * x) :
    (family p a).norm (primePoint p) (1 ⊗ₜ[ℚ] (![x, y] : Plane)) = 1 := by
  rw [family_norm_prime_rational]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hs : (y : ℚ) - (a : ℚ) * (x : ℚ) = ((y - a * x : ℤ) : ℚ) := by push_cast; rfl
  rw [hs, rational_primeValue_integer_eq_one p x
    (primitive_good_congruence_first_unit p a x y hxy hc)]
  apply max_eq_left
  apply (mul_le_mul_of_nonneg_left
    (rational_primeValue_integer_le_inv_of_dvd p (y - a * x) hc)
    (Real.sqrt_nonneg _)).trans
  rw [← div_eq_mul_inv]
  apply (div_le_one (by exact_mod_cast p.property.pos)).mpr
  have hp : (1 : ℝ) ≤ p.val := by exact_mod_cast p.property.one_le
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p.val)
  have hroot : 1 ≤ Real.sqrt (p.val : ℝ) := Real.one_le_sqrt.mpr hp
  nlinarith [mul_nonneg (Real.sqrt_nonneg (p.val : ℝ)) (sub_nonneg.mpr hroot)]

theorem rational_finite_primitive_max_eq_one (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (x y : ℤ) (hxy : IsCoprime x y) :
    max (S.ϕ ω (x : ℚ)) (S.ϕ ω (y : ℚ)) = 1 := by
  have hZ (n : ℤ) : S.ϕ ω (n : ℚ) ≤ 1 :=
    hω.apply_intCast_le_one (map_zero_le _ 1) (map_one _) (S.ϕ ω).map_neg
  apply le_antisymm (max_le (hZ x) (hZ y))
  obtain ⟨b, c, hb⟩ := hxy
  have hbq : (b : ℚ) * (x : ℚ) + (c : ℚ) * (y : ℚ) = 1 := by exact_mod_cast hb
  calc
    1 = S.ϕ ω ((b : ℚ) * (x : ℚ) + (c : ℚ) * (y : ℚ)) := by rw [hbq, map_one]
    _ ≤ max (S.ϕ ω ((b : ℚ) * (x : ℚ))) (S.ϕ ω ((c : ℚ) * (y : ℚ))) := hω _ _
    _ ≤ max (S.ϕ ω (x : ℚ)) (S.ϕ ω (y : ℚ)) := by
      simp only [map_mul]
      exact max_le_max
        (mul_le_of_le_one_left (apply_nonneg _ _) (hZ _))
        (mul_le_of_le_one_left (apply_nonneg _ _) (hZ _))

theorem family_norm_off_prime_integer_primitive (p : Nat.Primes) (a : ℤ)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) (hne : ω ≠ primePoint p)
    (x y : ℤ) (hxy : IsCoprime x y) :
    (family p a).norm ω (1 ⊗ₜ[ℚ] (![x, y] : Plane)) = 1 := by
  have hZ (n : ℤ) : S.ϕ ω (n : ℚ) ≤ 1 :=
    hω.apply_intCast_le_one (map_zero_le _ 1) (map_one _) (S.ϕ ω).map_neg
  rw [family_norm_off_prime p a ω hne,
    ofBasisHermitian_norm_of_finite standardBasis ω hω, ofBasis_norm_rational]
  simp only [standardBasis, Pi.basisFun_equivFun, LinearEquiv.refl_apply]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    fin_cases i
    · simpa only [Fin.zero_eta, Matrix.cons_val_zero, Real.norm_eq_abs,
        abs_of_nonneg (apply_nonneg _ _)] using
        (hZ x)
    · simpa only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs,
        abs_of_nonneg (apply_nonneg _ _)] using
        (hZ y)
  · rw [← rational_finite_primitive_max_eq_one ω hω x y hxy]
    apply max_le
    · simpa only [Matrix.cons_val_zero, Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
        using norm_le_pi_norm (fun i => S.ϕ ω ((![x, y] : Plane) i)) 0
    · simpa only [Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
        using norm_le_pi_norm (fun i => S.ϕ ω ((![x, y] : Plane) i)) 1

theorem family_norm_prime_axis_zero (p : Nat.Primes) (a : ℤ)
    (ha : (p.val : ℤ) ∣ a ^ 2 + 1) :
    (family p a).norm (primePoint p) (1 ⊗ₜ[ℚ] (![1, 0] : Plane)) =
      Real.sqrt (p.val : ℝ) := by
  have hc : ¬ (p.val : ℤ) ∣ (0 : ℤ) - a * 1 := by
    simpa only [mul_one, zero_sub, dvd_neg] using prime_not_dvd_root_minus_one p a ha
  simpa only [Int.cast_one, Int.cast_zero] using family_norm_prime_integer_bad p a 1 0 hc

theorem family_norm_prime_axis_one (p : Nat.Primes) (a : ℤ) :
    (family p a).norm (primePoint p) (1 ⊗ₜ[ℚ] (![0, 1] : Plane)) =
      Real.sqrt (p.val : ℝ) := by
  have hc : ¬ (p.val : ℤ) ∣ (1 : ℤ) - a * 0 := by
    intro h
    simp only [mul_zero, sub_zero] at h
    exact p.property.not_dvd_one (by exact_mod_cast h)
  simpa only [Int.cast_one, Int.cast_zero] using family_norm_prime_integer_bad p a 0 1 hc

theorem primitive_one_le_family_norm_finite (p : Nat.Primes) (a : ℤ)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) (x y : ℤ) (hxy : IsCoprime x y) :
    1 ≤ (family p a).norm ω (1 ⊗ₜ[ℚ] (![x, y] : Plane)) := by
  by_cases he : ω = primePoint p
  · subst ω
    by_cases hc : (p.val : ℤ) ∣ y - a * x
    · rw [family_norm_prime_integer_good p a x y hxy hc]
    · rw [family_norm_prime_integer_bad p a x y hc]
      exact Real.one_le_sqrt.mpr (by exact_mod_cast p.property.one_le)
  · rw [family_norm_off_prime_integer_primitive p a ω hω he x y hxy]

open Classical in
theorem family_norm_integer_primitive_profile (p : Nat.Primes) (a : ℤ)
    (ω : S.Ω) (x y : ℤ) (hxy : IsCoprime x y) :
    (family p a).norm ω (1 ⊗ₜ[ℚ] (![x, y] : Plane)) =
      if ω ∈ S.Ωinf then Real.sqrt ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)
      else if ω = primePoint p ∧ ¬ (p.val : ℤ) ∣ y - a * x
        then Real.sqrt (p.val : ℝ) else 1 := by
  by_cases hi : ω ∈ S.Ωinf
  · rw [ite_eq_left hi, family_norm_infinite_integer p a ω hi]
  · rw [ite_eq_right hi]
    have hf : ω ∈ S.Ωfin := not_not.mp hi
    by_cases he : ω = primePoint p
    · subst ω
      by_cases hc : (p.val : ℤ) ∣ y - a * x
      · rw [family_norm_prime_integer_good p a x y hxy hc]
        simp only [hc, not_true_eq_false, and_false, ite_false]
      · rw [family_norm_prime_integer_bad p a x y hc]
        simp only [hc, not_false_eq_true, and_self, ite_true]
    · rw [family_norm_off_prime_integer_primitive p a ω hf he x y hxy]
      simp only [he, false_and, ite_false]

end ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

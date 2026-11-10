/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormFamilyNormalizedPrimeIndexing
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The actual normalized completion degree and arithmetic ramification

The rationally normalized curve and its finite power comparison are already
produced. Evaluate that comparison at its actual rational base prime to identify
the actual completed local degree with canonical ramification times inertia.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ArakelovGeometry.ActualPrimeIndexing

open AdelicStructure AdelicStructure.NormalizedNumberFieldPlaces

variable {K : Type*} [Field K] [NumberField K]

/-- The actual base of an actual finite normalized parameter is a rational prime. -/
theorem normalizedPrimeParameter_exists_base_prime (P : HeightOneSpectrum (𝓞 K)) :
    ∃ p : Nat.Primes,
      (parameterMeasurableEquivNontrivialPlace.symm (normalizedPrimeParameter P)).base =
        Sum.inl p := by
  have hna := normalizedPrimeParameter_mem_fin P
  have hrestriction : IsNonarchimedean
      ((normalizedPlaceValue (normalizedPrimeParameter P)).under ℚ) := by
    intro a b
    change normalizedPlaceValue (normalizedPrimeParameter P) (algebraMap ℚ K (a + b)) ≤
      max (normalizedPlaceValue (normalizedPrimeParameter P) (algebraMap ℚ K a))
        (normalizedPlaceValue (normalizedPrimeParameter P) (algebraMap ℚ K b))
    rw [map_add]
    exact hna _ _
  have hbaseNA : IsNonarchimedean (rationalAdelicStructure.ϕ
      (parameterMeasurableEquivNontrivialPlace.symm (normalizedPrimeParameter P)).base) :=
    (congrArg (fun v : AbsoluteValue ℚ ℝ => IsNonarchimedean v)
      (normalizedPlaceValue_restriction_rat (normalizedPrimeParameter P))).mp hrestriction
  cases hb : (parameterMeasurableEquivNontrivialPlace.symm
      (normalizedPrimeParameter P)).base with
  | inl p => exact ⟨p, rfl⟩
  | inr u =>
    cases u
    with_reducible rw [hb] at hbaseNA
    exact False.elim (rationalAdelicStructure_infinite_mem_inf hbaseNA)

/-- Exact normalization produces the arithmetic lies-over relation at the actual base. -/
theorem normalizedPrimeParameter_liesOver_base (P : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (hp : (parameterMeasurableEquivNontrivialPlace.symm
      (normalizedPrimeParameter P)).base = Sum.inl p) :
    P.asIdeal.LiesOver (Ideal.span {(p.val : ℤ)}) := by
  let hpFact : Fact p.val.Prime := ⟨p.property⟩
  have hp1 : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hα : normalizedPlaceValue (normalizedPrimeParameter P) (p.val : K) < 1 := by
    rw [normalizedPlaceValue_apply_base_prime _ p hp]
    exact (inv_lt_one₀ (by positivity)).mpr hp1
  have hd : (0 : ℝ) <
      ((normalizedPlaceValue (normalizedPrimeParameter P)).localDegree ℚ : ℝ) := by
    exact_mod_cast normalizedPlaceValue_finitePlace_localDegree_pos (FinitePlace.mk P)
  have hβ : (FinitePlace.mk P) (p.val : K) < 1 := by
    rw [← normalizedPlaceValue_rpow_localDegree_finitePlace]
    exact Real.rpow_lt_one (apply_nonneg _ _) hα hd
  have hmem : (p.val : 𝓞 K) ∈ P.asIdeal := by
    apply (FinitePlace.norm_lt_one_iff_mem K P _).mp
    have hn := FinitePlace.norm_embedding_eq (FinitePlace.mk P) (p.val : K)
    rw [FinitePlace.maximalIdeal_mk] at hn
    have hh : ‖FinitePlace.embedding P (p.val : K)‖ < 1 := lt_of_eq_of_lt hn hβ
    simpa only [map_natCast] using hh
  apply (Ideal.liesOver_iff_dvd_map P.isPrime.ne_top).mpr
  rw [Ideal.dvd_iff_le, Ideal.map_span, Set.image_singleton]
  apply (Ideal.span_singleton_le_iff_mem P.asIdeal).mpr
  with_reducible simpa only [map_natCast, map_intCast, Int.cast_natCast] using hmem

/-- The canonical residue degree computes the actual absolute ideal norm. -/
theorem absNorm_eq_pow_canonical_inertiaDeg (P : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes) [P.asIdeal.LiesOver (Ideal.span {(p.val : ℤ)})] :
    Ideal.absNorm P.asIdeal = p.val ^ P.asIdeal.inertiaDeg ℤ := by
  simpa only [Int.natAbs_natCast] using
    (Ideal.natAbs_pow_inertiaDeg (p.val : ℤ) P.asIdeal).symm

/-- At actual integral primes the canonical residue degree is strictly positive. -/
theorem canonical_inertiaDeg_pos (P : HeightOneSpectrum (𝓞 K)) :
    0 < P.asIdeal.inertiaDeg ℤ := Ideal.inertiaDeg_pos P.asIdeal ℤ

/-- The canonical inertia degree agrees with the actual quotient residue-field dimension. -/
theorem canonical_inertiaDeg_eq_quotient_finrank (P : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes) [P.asIdeal.LiesOver (Ideal.span {(p.val : ℤ)})] :
    P.asIdeal.inertiaDeg ℤ =
      Module.finrank (ℤ ⧸ Ideal.span {(p.val : ℤ)}) ((𝓞 K) ⧸ P.asIdeal) := by
  let hpFact : Fact p.val.Prime := ⟨p.property⟩
  exact Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {(p.val : ℤ)}) P.asIdeal

/-- At actual integral primes the canonical ramification index is strictly positive. -/
theorem canonical_ramificationIdx_pos (P : HeightOneSpectrum (𝓞 K)) :
    0 < P.asIdeal.ramificationIdx ℤ := Ideal.ramificationIdx_pos ℤ P.asIdeal

/-- The signed actual adic exponent of the base prime is minus the canonical ramification index. -/
theorem valuation_log_base_prime_eq_neg_ramificationIdx (P : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes) [P.asIdeal.LiesOver (Ideal.span {(p.val : ℤ)})] :
    (P.valuation K (p.val : K)).log = -(P.asIdeal.ramificationIdx ℤ : ℤ) := by
  have hp0 : (p.val : 𝓞 K) ≠ 0 := by
    exact_mod_cast p.property.ne_zero
  have hm : (Ideal.span {(p.val : ℤ)}).map (algebraMap ℤ (𝓞 K)) =
      Ideal.span {(p.val : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun r : 𝓞 K => Ideal.span {r})
      (map_natCast (algebraMap ℤ (𝓞 K)) p.val)
  have he : P.asIdeal.ramificationIdx ℤ =
      multiplicity P.asIdeal (Ideal.span {(p.val : 𝓞 K)}) := by
    apply (Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
      (Ideal.span {(p.val : ℤ)}) P.asIdeal ?_).trans
      (congrArg (multiplicity P.asIdeal) hm)
    rw [hm]
    exact fun h => hp0 (Ideal.span_singleton_eq_bot.mp h)
  have hv : P.valuation K (p.val : K) = P.intValuation (p.val : 𝓞 K) := by
    simpa only [map_natCast] using P.valuation_of_algebraMap (K := K) (p.val : 𝓞 K)
  rw [hv, P.intValuation_eq_exp_neg_multiplicity hp0, WithZero.log_exp, he]

/-- The actual completed local degree is canonical ramification times canonical residue degree. -/
theorem normalizedPrime_localDegree_eq_ramificationIdx_mul_inertiaDeg
    (P : HeightOneSpectrum (𝓞 K)) :
    (normalizedPlaceValue (normalizedPrimeParameter P)).localDegree ℚ =
      P.asIdeal.ramificationIdx ℤ * P.asIdeal.inertiaDeg ℤ := by
  obtain ⟨p, hp⟩ := normalizedPrimeParameter_exists_base_prime P
  let hLiesOver : P.asIdeal.LiesOver (Ideal.span {(p.val : ℤ)}) :=
    normalizedPrimeParameter_liesOver_base P p hp
  have hpK : (p.val : K) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hp1 : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hlogp : Real.log (p.val : ℝ) ≠ 0 := (Real.log_pos hp1).ne'
  have hvalue := normalizedPlaceValue_apply_base_prime (normalizedPrimeParameter P) p hp
  have hweighted := normalizedPlaceValue_weightedLog_finitePlace (FinitePlace.mk P) hpK
  have hvaluation : ((P.valuation K (p.val : K)).log : ℝ) =
      -(P.asIdeal.ramificationIdx ℤ : ℝ) := by
    exact_mod_cast valuation_log_base_prime_eq_neg_ramificationIdx P p
  have hnorm : Real.log (Ideal.absNorm P.asIdeal : ℝ) =
      (P.asIdeal.inertiaDeg ℤ : ℝ) * Real.log (p.val : ℝ) := by
    rw [absNorm_eq_pow_canonical_inertiaDeg P p, Nat.cast_pow, Real.log_pow]
  have hβlog := finitePlace_log_value P hpK
  rw [hvaluation, hnorm] at hβlog
  change ((normalizedPlaceValue (normalizedPrimeParameter P)).localDegree ℚ : ℝ) *
      Real.log (normalizedPlaceValue (normalizedPrimeParameter P) (p.val : K)) =
      Real.log ((FinitePlace.mk P) (p.val : K)) at hweighted
  rw [hvalue, Real.log_inv, hβlog] at hweighted
  have hc : ((normalizedPlaceValue (normalizedPrimeParameter P)).localDegree ℚ : ℝ) *
      Real.log (p.val : ℝ) =
      ((P.asIdeal.ramificationIdx ℤ * P.asIdeal.inertiaDeg ℤ : ℕ) : ℝ) *
        Real.log (p.val : ℝ) := by
    push_cast
    nlinarith [hweighted]
  exact_mod_cast mul_right_cancel₀ hlogp hc

/-- The actual normalized finite-place atom is the canonical arithmetic local degree. -/
theorem normalizedPrime_mass_eq_ramificationIdx_mul_inertiaDeg
    (P : HeightOneSpectrum (𝓞 K)) :
    (normalizedNumberFieldAdelicStructure K).v {normalizedPrimeParameter P} =
      ((P.asIdeal.ramificationIdx ℤ * P.asIdeal.inertiaDeg ℤ : ℕ) : ENNReal) := by
  exact (normalizedNumberFieldAdelicStructure_v_singleton (normalizedPrimeParameter P)).trans
    (congrArg (fun n : ℕ => (n : ENNReal))
      (normalizedPrime_localDegree_eq_ramificationIdx_mul_inertiaDeg P))

/-- The actual normalized finite value is the inverse arithmetic-degree power of the old value. -/
theorem normalizedPrime_value_eq_rpow_inverse_ramificationIdx_mul_inertiaDeg
    (P : HeightOneSpectrum (𝓞 K)) (a : K) :
    normalizedPlaceValue (normalizedPrimeParameter P) a =
      (FinitePlace.mk P a) ^
        (((P.asIdeal.ramificationIdx ℤ * P.asIdeal.inertiaDeg ℤ : ℕ) : ℝ)⁻¹) := by
  have h := normalizedPlaceValue_eq_finitePlace_rpow (FinitePlace.mk P) a
  change normalizedPlaceValue (normalizedPrimeParameter P) a =
      (FinitePlace.mk P a) ^
        (((normalizedPlaceValue (normalizedPrimeParameter P)).localDegree ℚ : ℝ)⁻¹) at h
  exact h.trans (congrArg (fun d : ℕ => (FinitePlace.mk P a) ^ ((d : ℝ)⁻¹))
    (normalizedPrime_localDegree_eq_ramificationIdx_mul_inertiaDeg P))

end ArakelovGeometry.ActualPrimeIndexing

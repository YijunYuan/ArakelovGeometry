/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.ValuationModuleFinite
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# Actual fractions with a pole at one prescribed prime

The inverse of an actual nonzero prime ideal produces a fraction with a simple
pole at that prime and no poles elsewhere. These arithmetic producers feed the
necessity direction of Chen–Moriwaki, Lemma 4.4.7, PDF page309.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.FiniteValuation

open IsDedekindDomain
open scoped WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Inverse-prime membership makes products by original prime elements integral. -/
theorem valuation_mul_le_one_of_mem_inv_prime (p : HeightOneSpectrum R) {x : K}
    (hx : x ∈ (p.asIdeal : FractionalIdeal (nonZeroDivisors R) K)⁻¹)
    {r : R} (hr : r ∈ p.asIdeal) (q : HeightOneSpectrum R) :
    q.valuation K x * q.valuation K (algebraMap R K r) ≤ 1 := by
  have hP0 : (p.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot
  have hprod := (FractionalIdeal.mem_inv_iff hP0).mp hx (algebraMap R K r)
    (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors R) hr)
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (nonZeroDivisors R)).mp hprod
  rw [← map_mul, ← ha]
  exact q.valuation_le_one (K := K) a

/-- An actual element of the inverse prime ideal has no pole at another prime. -/
theorem valuation_le_one_of_mem_inv_prime_of_ne (p q : HeightOneSpectrum R) {x : K}
    (hx : x ∈ (p.asIdeal : FractionalIdeal (nonZeroDivisors R) K)⁻¹) (hpq : p ≠ q) :
    q.valuation K x ≤ 1 := by
  have hnot : ¬p.asIdeal ≤ q.asIdeal := by
    intro h
    apply hpq
    exact HeightOneSpectrum.asIdeal_injective
      ((Ring.DimensionLeOne.prime_le_prime_iff_eq p.ne_bot).mp h)
  obtain ⟨r, hrp, hrq⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hqr : q.valuation K (algebraMap R K r) = 1 := by
    rw [q.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hrq
  simpa only [hqr, mul_one] using valuation_mul_le_one_of_mem_inv_prime p hx hrp q

/-- At the original prime, inverse-ideal membership allows at most a simple pole. -/
theorem valuation_le_exp_one_of_mem_inv_prime (p : HeightOneSpectrum R) {x : K}
    (hx : x ∈ (p.asIdeal : FractionalIdeal (nonZeroDivisors R) K)⁻¹) :
    p.valuation K x ≤ WithZero.exp (1 : ℤ) := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer' K
  have hπmem : π ∈ p.asIdeal := by
    apply (p.valuation_lt_one_iff_mem (K := K) π).mp
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    decide
  have hmul := valuation_mul_le_one_of_mem_inv_prime p hx hπmem p
  rw [hπ] at hmul
  have h := mul_le_mul hmul (le_rfl : WithZero.exp (1 : ℤ) ≤ WithZero.exp (1 : ℤ))
    zero_le zero_le
  simpa only [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero,
    mul_one, one_mul] using h

/-- A genuine fraction with a pole at exactly one prescribed prime is produced. -/
theorem exists_single_prime_pole (p : HeightOneSpectrum R) :
    ∃ x : K, 1 < p.valuation K x ∧ p.valuation K x ≤ WithZero.exp (1 : ℤ) ∧
      ∀ q : HeightOneSpectrum R, q ≠ p → q.valuation K x ≤ 1 := by
  let P : FractionalIdeal (nonZeroDivisors R) K := p.asIdeal
  have hP1 : P ≠ 1 := FractionalIdeal.coeIdeal_ne_one.mpr (by
    simpa only [Ideal.one_eq_top] using p.isPrime.ne_top)
  have hnot : ¬P⁻¹ ≤ 1 := by
    intro hle
    have h1 : (1 : FractionalIdeal (nonZeroDivisors R) K) ≤ P := by
      calc
        1 = P * P⁻¹ := (FractionalIdeal.coe_ideal_mul_inv (K := K) p.asIdeal p.ne_bot).symm
        _ ≤ P * 1 := mul_right_mono hle
        _ = P := mul_one P
    exact hP1 (le_antisymm FractionalIdeal.coeIdeal_le_one h1)
  obtain ⟨x, hx, hxnot⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hout (q : HeightOneSpectrum R) (hqp : q ≠ p) : q.valuation K x ≤ 1 :=
    valuation_le_one_of_mem_inv_prime_of_ne p q hx hqp.symm
  refine ⟨x, ?_, valuation_le_exp_one_of_mem_inv_prime p hx, hout⟩
  by_contra h
  apply hxnot
  apply (FractionalIdeal.mem_one_iff (nonZeroDivisors R)).mpr
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro q
  by_cases hqp : q = p
  · subst q
    exact le_of_not_gt h
  · exact hout q hqp

/-- Finite negative support produces a nonzero original-ring element in the actual module. -/
theorem exists_ring_mem_valuationModule_of_finite_negative {b : HeightOneSpectrum R → ℤ}
    (hb : {v | b v < 0}.Finite) :
    ∃ a : R, a ≠ 0 ∧ algebraMap R K a ∈ valuationModule (K := K) b := by
  have hneg : {v | 0 < -b v}.Finite := by simpa only [neg_pos] using hb
  obtain ⟨a, ha, hav⟩ :=
    exists_valuation_denominator_of_finite_positive (K := K) hneg
  refine ⟨a, ha, ?_⟩
  intro v
  have h := mul_le_mul (hav v)
    (le_rfl : WithZero.exp (b v) ≤ WithZero.exp (b v)) zero_le zero_le
  simpa only [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero,
    mul_one, one_mul] using h

/-- A positive prime beyond an original-ring member's support admits an actual module pole. -/
theorem exists_valuationModule_pole_of_ring_member {b : HeightOneSpectrum R → ℤ}
    {a : R} (ha : algebraMap R K a ∈ valuationModule (K := K) b)
    (p : HeightOneSpectrum R) (hp : 0 < b p)
    (hap : p.valuation K (algebraMap R K a) = 1) :
    ∃ x ∈ valuationModule (K := K) b, 1 < p.valuation K x := by
  obtain ⟨y, hy, hyp, hout⟩ := exists_single_prime_pole (K := K) p
  refine ⟨algebraMap R K a * y, ?_, ?_⟩
  · intro q
    rw [map_mul]
    by_cases hqp : q = p
    · subst q
      rw [hap, one_mul]
      exact hyp.trans (WithZero.exp_le_exp.mpr (Int.add_one_le_iff.mpr hp))
    · exact (mul_le_mul le_rfl (hout q hqp) zero_le zero_le).trans
        (by simpa only [mul_one] using ha q)
  · simpa only [map_mul, hap, one_mul] using hy

/-- With finite negative support, actual finite generation forces finite positive support. -/
theorem finite_positive_of_fg_valuationModule_of_finite_negative
    {b : HeightOneSpectrum R → ℤ} (hfg : (valuationModule (K := K) b).FG)
    (hb : {v | b v < 0}.Finite) : {v | 0 < b v}.Finite := by
  obtain ⟨a, ha, hamem⟩ := exists_ring_mem_valuationModule_of_finite_negative (K := K) hb
  obtain ⟨d, hd, hden⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) hfg
  have haK : algebraMap R K a ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne ha
  have hdR : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hdK : algebraMap R K d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hdR
  apply ((finite_valuation_ne_one (R := R) haK).union
    (finite_valuation_ne_one (R := R) hdK)).subset
  intro p hp
  by_contra hout
  have hap : p.valuation K (algebraMap R K a) = 1 := by
    by_contra hne
    exact hout (Or.inl hne)
  have hdp : p.valuation K (algebraMap R K d) = 1 := by
    by_contra hne
    exact hout (Or.inr hne)
  obtain ⟨x, hx, hxp⟩ := exists_valuationModule_pole_of_ring_member hamem p hp hap
  obtain ⟨c, hc⟩ := hden x hx
  have hbound := p.valuation_le_one (K := K) c
  change p.valuation K (algebraMap R K c) ≤ 1 at hbound
  rw [hc, Algebra.smul_def, map_mul, hdp, one_mul] at hbound
  exact (not_lt_of_ge hbound) hxp

/-- The full actual valuation-module finite-generation criterion of Lemma 4.4.7. -/
theorem fg_valuationModule_iff {b : HeightOneSpectrum R → ℤ} :
    (valuationModule (K := K) b).FG ↔
      {v | 0 < b v}.Finite ∨ {v | b v < 0}.Infinite := by
  constructor
  · intro hfg
    by_cases hb : {v | b v < 0}.Finite
    · exact Or.inl (finite_positive_of_fg_valuationModule_of_finite_negative hfg hb)
    · exact Or.inr hb
  · rintro (hpos | hneg)
    · exact fg_valuationModule_of_finite_positive hpos
    · exact fg_valuationModule_of_infinite_negative hneg

end ArakelovGeometry.FiniteValuation

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Local.ValuationModule.Basic

/-!
# Common denominators for finitely many positive prime bounds

Finite positive support of an integer bound family produces a nonzero actual
denominator in the original Dedekind domain. The actual valuation submodule
is therefore fractional and finitely generated. Negative support is unrestricted.

Reference: Chen–Moriwaki, Lemma 4.4.7, PDF page 309.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.FiniteValuation

open IsDedekindDomain
open scoped BigOperators WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Finite positive support produces simultaneous actual denominator bounds. -/
theorem exists_valuation_denominator_of_finite_positive {b : HeightOneSpectrum R → ℤ}
    (hb : {v | 0 < b v}.Finite) :
    ∃ a : R, a ≠ 0 ∧ ∀ v, v.valuation K (algebraMap R K a) * WithZero.exp (b v) ≤ 1 := by
  classical
  let s := hb.toFinset
  choose π hπ using fun v : HeightOneSpectrum R => v.valuation_exists_uniformizer' K
  have hπ0 (v : HeightOneSpectrum R) : π v ≠ 0 := by
    intro h
    apply WithZero.exp_ne_zero (a := (-1 : ℤ))
    rw [← hπ v, h]
    simp
  let a := ∏ v ∈ s, π v ^ (b v).toNat
  refine ⟨a, Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (hπ0 v)), ?_⟩
  intro v
  by_cases hv : 0 < b v
  · have hvs : v ∈ s := hb.mem_toFinset.mpr hv
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun w => π w ^ (b w).toNat) hvs
    have hn : (b v).toNat • (-1 : ℤ) = -b v := by
      simp [Int.toNat_of_nonneg (le_of_lt hv)]
    have hpow : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ^ (b v).toNat = WithZero.exp (-b v) := by
      rw [← WithZero.exp_nsmul, hn]
    change v.valuation K (algebraMap R K (∏ w ∈ s, π w ^ (b w).toNat)) * _ ≤ _
    rw [hr, map_mul, map_mul, map_pow, map_pow, hπ v, hpow]
    calc
      WithZero.exp (-b v) * v.valuation K (algebraMap R K r) * WithZero.exp (b v)
          ≤ WithZero.exp (-b v) * 1 * WithZero.exp (b v) :=
        mul_le_mul (mul_le_mul le_rfl (v.valuation_le_one (K := K) r) zero_le zero_le)
          le_rfl zero_le zero_le
      _ = 1 := by rw [mul_one, ← WithZero.exp_add]; simp
  · exact (mul_le_mul (v.valuation_le_one (K := K) a)
      (by simpa only [← WithZero.exp_zero, WithZero.exp_le_exp] using le_of_not_gt hv)
      zero_le zero_le).trans_eq (one_mul 1)

/-- The denominator sends the entire actual valuation module into the original ring. -/
theorem exists_common_denominator_of_finite_positive {b : HeightOneSpectrum R → ℤ}
    (hb : {v | 0 < b v}.Finite) :
    ∃ a : R, a ≠ 0 ∧ ∀ x ∈ valuationModule (K := K) b,
      (algebraMap R K a) * x ∈ (algebraMap R K).range := by
  obtain ⟨a, ha, hav⟩ := exists_valuation_denominator_of_finite_positive (K := K) hb
  refine ⟨a, ha, ?_⟩
  intro x hx
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro v
  rw [map_mul]
  exact (mul_le_mul le_rfl (hx v) zero_le zero_le).trans (hav v)

/-- Finite positive support makes the actual submodule a canonical fractional ideal. -/
theorem isFractional_valuationModule_of_finite_positive {b : HeightOneSpectrum R → ℤ}
    (hb : {v | 0 < b v}.Finite) :
    IsFractional (nonZeroDivisors R) (valuationModule (K := K) b) := by
  obtain ⟨a, ha, hax⟩ := exists_common_denominator_of_finite_positive (K := K) hb
  refine ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha, ?_⟩
  intro x hx
  rw [Algebra.smul_def]
  exact hax x hx

/-- The finite-positive case of the finite-generation criterion in Lemma 4.4.7. -/
theorem fg_valuationModule_of_finite_positive {b : HeightOneSpectrum R → ℤ}
    (hb : {v | 0 < b v}.Finite) : (valuationModule (K := K) b).FG := by
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl
    ⟨valuationModule (K := K) b, isFractional_valuationModule_of_finite_positive hb⟩

end ArakelovGeometry.FiniteValuation

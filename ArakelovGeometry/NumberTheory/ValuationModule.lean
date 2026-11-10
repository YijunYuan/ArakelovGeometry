/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Modules defined by integer prime-valuation constraints

For a Dedekind domain and its actual fraction field, `valuationModule b`
is the submodule defined by the inequalities `ord_v(x) + b v ≥ 0`.
Nonzero scalars have finite prime-valuation support. Consequently infinitely
many negative constraints force the actual module to be zero.

Reference: Chen–Moriwaki, Lemma 4.4.7, PDF pages 308–309. These arithmetic
results use prime orders independently of finite-place normalization.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.FiniteValuation

open IsDedekindDomain
open scoped WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual module with the integer prime-order bounds `ord_v(x) + b v ≥ 0`. -/
def valuationModule (b : HeightOneSpectrum R → ℤ) : Submodule R K where
  carrier := {x | ∀ v, v.valuation K x ≤ WithZero.exp (b v)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy v
    exact (v.valuation K).map_add x y |>.trans (max_le (hx v) (hy v))
  smul_mem' := by
    intro r x hx v
    rw [Algebra.smul_def]
    calc
      v.valuation K ((algebraMap R K r) * x) =
          v.valuation K (algebraMap R K r) * v.valuation K x := map_mul _ _ _
      _ ≤ 1 * WithZero.exp (b v) :=
        mul_le_mul (v.valuation_le_one (K := K) r) (hx v) zero_le zero_le
      _ = WithZero.exp (b v) := one_mul _

@[simp]
theorem mem_valuationModule_iff {b : HeightOneSpectrum R → ℤ} {x : K} :
    x ∈ valuationModule (K := K) b ↔ ∀ v, v.valuation K x ≤ WithZero.exp (b v) :=
  Iff.rfl

/-- Increasing each integer bound enlarges the actual valuation module. -/
theorem valuationModule_mono {b c : HeightOneSpectrum R → ℤ} (h : b ≤ c) :
    valuationModule (K := K) b ≤ valuationModule (K := K) c := by
  intro x hx v
  exact (hx v).trans (WithZero.exp_le_exp.mpr (h v))

/-- A nonzero actual fraction-field element has only finitely many nonunit valuations. -/
theorem finite_valuation_ne_one {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum R | v.valuation K x ≠ 1}.Finite := by
  classical
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective R x
  have ha : a ≠ 0 := by
    intro h
    apply hx
    simp [h]
  have hd' : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hIa : (Ideal.span {a} : Ideal R) ≠ 0 := by simpa using ha
  have hId : (Ideal.span {d} : Ideal R) ≠ 0 := by simpa using hd'
  apply ((Ideal.finite_factors hIa).union (Ideal.finite_factors hId)).subset
  intro v hv
  by_contra h
  have hna : a ∉ v.asIdeal := by
    intro hmem
    exact h (Or.inl (Ideal.dvd_span_singleton.mpr hmem))
  have hnd : d ∉ v.asIdeal := by
    intro hmem
    exact h (Or.inr (Ideal.dvd_span_singleton.mpr hmem))
  apply hv
  rw [map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hna,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hnd, div_one]

/-- Infinitely many negative integer constraints force the actual submodule to be zero. -/
theorem valuationModule_eq_bot_of_infinite_negative {b : HeightOneSpectrum R → ℤ}
    (hb : {v | b v < 0}.Infinite) : valuationModule (K := K) b = ⊥ := by
  apply le_antisymm
  · intro x hx
    apply (Submodule.mem_bot R).mpr
    by_contra hne
    apply hb
    apply (finite_valuation_ne_one (R := R) hne).subset
    intro v hv
    change b v < 0 at hv
    have hexp : WithZero.exp (b v) < (1 : ℤᵐ⁰) := by
      simpa only [← WithZero.exp_zero, WithZero.exp_lt_exp] using hv
    exact ne_of_lt ((hx v).trans_lt hexp)
  · exact bot_le

/-- The infinite-negative case of the finite-generation criterion in Lemma 4.4.7. -/
theorem fg_valuationModule_of_infinite_negative {b : HeightOneSpectrum R → ℤ}
    (hb : {v | b v < 0}.Infinite) : (valuationModule (K := K) b).FG := by
  rw [valuationModule_eq_bot_of_infinite_negative hb]
  exact Submodule.fg_bot

end ArakelovGeometry.FiniteValuation

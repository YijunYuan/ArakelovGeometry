/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module


public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# An algebraic integer supported on prescribed finite primes

The finite ideal class group makes the class-number power of an actual product
of nonzero prime ideals principal. Its generator realizes Claim 4.4.3(a) of
Chen–Moriwaki, PDF page 306, in the actual ring of integers of a number field.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.PrincipalPrimeSupport

open IsDedekindDomain
open scoped NumberField nonZeroDivisors WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The product of finitely many actual nonzero prime ideals is nonzero. -/
theorem primeIdealProduct_ne_zero (s : Finset (HeightOneSpectrum R)) :
    (∏ p ∈ s, p.asIdeal) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun p _ => p.ne_bot)

open Classical in
/-- Prime ideals occur with multiplicity one in themselves, and zero in other primes. -/
theorem emultiplicity_asIdeal_asIdeal (p q : HeightOneSpectrum R) :
    emultiplicity p.asIdeal q.asIdeal = if q = p then 1 else 0 := by
  classical
  by_cases hqp : q = p
  · subst q
    simpa using emultiplicity_pow_self_of_prime p.prime 1
  · rw [ite_eq_right hqp, emultiplicity_eq_zero]
    intro hdvd
    apply hqp
    apply HeightOneSpectrum.asIdeal_injective
    exact (associated_iff_eq.mp ((p.prime.dvd_prime_iff_associated q.prime).mp hdvd)).symm

open Classical in
/-- A finite prime product has multiplicity one exactly at its selected primes. -/
theorem emultiplicity_primeIdealProduct (s : Finset (HeightOneSpectrum R))
    (p : HeightOneSpectrum R) :
    emultiplicity p.asIdeal (∏ q ∈ s, q.asIdeal) = if p ∈ s then 1 else 0 := by
  classical
  rw [Finset.emultiplicity_prod p.prime]
  simp_rw [emultiplicity_asIdeal_asIdeal]
  exact Finset.sum_ite_eq' s p (fun _ => (1 : ℕ∞))

open Classical in
/-- The exact finite multiplicities in a positive or zeroth power of the prime product. -/
theorem multiplicity_primeIdealProduct_pow (s : Finset (HeightOneSpectrum R))
    (p : HeightOneSpectrum R) (n : ℕ) :
    multiplicity p.asIdeal ((∏ q ∈ s, q.asIdeal) ^ n) = if p ∈ s then n else 0 := by
  classical
  have hfm := FiniteMultiplicity.of_prime_left p.prime (primeIdealProduct_ne_zero s)
  rw [hfm.multiplicity_pow p.prime]
  have hbase : multiplicity p.asIdeal (∏ q ∈ s, q.asIdeal) = if p ∈ s then 1 else 0 := by
    apply ENat.natCast_inj.mp
    rw [← hfm.emultiplicity_eq_multiplicity, emultiplicity_primeIdealProduct]
    split_ifs <;> rfl
  rw [hbase]
  split_ifs <;> simp

/-- The actual finite class group makes a class-number power of any nonzero ideal principal. -/
theorem exists_generator_pow_card_classGroup [Fintype (ClassGroup R)]
    (I : Ideal R) (hI : I ≠ 0) :
    ∃ f : R, f ≠ 0 ∧ Ideal.span {f} = I ^ Fintype.card (ClassGroup R) := by
  let hI0 : I ∈ (Ideal R)⁰ := mem_nonZeroDivisors_of_ne_zero hI
  have hclass : ClassGroup.mk0 (⟨I, hI0⟩ : (Ideal R)⁰) ^
      Fintype.card (ClassGroup R) = 1 := pow_card_eq_one
  have hprincipal : (I ^ Fintype.card (ClassGroup R)).IsPrincipal := by
    apply (ClassGroup.mk0_eq_one_iff (pow_mem hI0 _)).mp
    simpa only [← map_pow, SubmonoidClass.mk_pow] using hclass
  obtain ⟨f, hf⟩ := (Submodule.isPrincipal_iff _).mp hprincipal
  rw [Ideal.submodule_span_eq] at hf
  refine ⟨f, ?_, hf.symm⟩
  intro hf0
  have hpow0 : I ^ Fintype.card (ClassGroup R) = 0 := by simp [hf, hf0]
  exact pow_ne_zero _ hI hpow0

variable (K : Type*) [Field K] [NumberField K]

/-- The actual prime product in the ring of integers has a principal class-number power. -/
theorem exists_numberField_principal_prime_support (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ f : 𝓞 K, f ≠ 0 ∧ Ideal.span {f} = (∏ p ∈ s, p.asIdeal) ^ NumberField.classNumber K := by
  exact exists_generator_pow_card_classGroup _ (primeIdealProduct_ne_zero s)

open Classical in
/-- The integer order, defined by actual ideal multiplicity, is exactly the class number on
the selected set and zero at every other actual prime. -/
theorem exists_numberField_integer_order_support (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ f : 𝓞 K, f ≠ 0 ∧ ∀ p : HeightOneSpectrum (𝓞 K),
      (multiplicity p.asIdeal (Ideal.span {f}) : ℤ) =
        if p ∈ s then (NumberField.classNumber K : ℤ) else 0 := by
  classical
  obtain ⟨f, hf, hspan⟩ := exists_numberField_principal_prime_support K s
  refine ⟨f, hf, fun p => ?_⟩
  rw [hspan, multiplicity_primeIdealProduct_pow]
  split_ifs <;> rfl

/-- Claim 4.4.3(a): a genuine nonzero algebraic integer with precisely the prescribed
finite positive integer-order support. -/
theorem exists_numberField_positive_order_support (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ f : 𝓞 K, f ≠ 0 ∧
      (∀ p : HeightOneSpectrum (𝓞 K),
        0 < (multiplicity p.asIdeal (Ideal.span {f}) : ℤ) ↔ p ∈ s) ∧
      ∀ p : HeightOneSpectrum (𝓞 K), p ∉ s →
        (multiplicity p.asIdeal (Ideal.span {f}) : ℤ) = 0 := by
  classical
  obtain ⟨f, hf, hord⟩ := exists_numberField_integer_order_support K s
  refine ⟨f, hf, ?_, ?_⟩
  · intro p
    rw [hord p]
    by_cases hp : p ∈ s
    · simp only [hp, ite_true, iff_true]
      exact_mod_cast NumberField.classNumber_pos K
    · simp [hp]
  · intro p hp
    rw [hord p, ite_eq_right hp]

open Classical in
/-- The same actual integer has the exact multiplicative adic values determined by its orders. -/
theorem exists_numberField_intValuation_support (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ f : 𝓞 K, f ≠ 0 ∧
      (∀ p : HeightOneSpectrum (𝓞 K), p.intValuation f =
        if p ∈ s then WithZero.exp (-(NumberField.classNumber K : ℤ)) else 1) ∧
      ∀ p : HeightOneSpectrum (𝓞 K), p.intValuation f < 1 ↔ p ∈ s := by
  classical
  obtain ⟨f, hf, hord⟩ := exists_numberField_integer_order_support K s
  have hval (p : HeightOneSpectrum (𝓞 K)) : p.intValuation f =
      if p ∈ s then WithZero.exp (-(NumberField.classNumber K : ℤ)) else 1 := by
    rw [p.intValuation_eq_exp_neg_multiplicity hf, hord p]
    split_ifs <;> simp
  refine ⟨f, hf, hval, fun p => ?_⟩
  rw [hval p]
  by_cases hp : p ∈ s
  · simp only [hp, ite_true, iff_true]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp, neg_lt_zero]
    exact_mod_cast NumberField.classNumber_pos K
  · simp [hp]

end ArakelovGeometry.PrincipalPrimeSupport

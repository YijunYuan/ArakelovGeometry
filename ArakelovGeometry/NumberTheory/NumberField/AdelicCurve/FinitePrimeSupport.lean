/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.PrimeIndexing
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Basic

/-!
# Actual normalized integers with prescribed finite-place support

Products of the accepted actual isolated-prime integers give the literal
source finite-place support conclusion, including an empty exceptional set.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ArakelovGeometry.ActualPrimeIndexing

open AdelicStructure

variable {K : Type*} [Field K] [NumberField K]

/-- A produced nonzero integer contracts exactly at prescribed actual primes,
and has value one at every other actual normalized finite prime. -/
theorem exists_normalized_integral_prime_support
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ f : 𝓞 K, f ≠ 0 ∧
      (∀ p : HeightOneSpectrum (𝓞 K),
        (normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)
            (algebraMap (𝓞 K) K f) < 1 ↔ p ∈ s) ∧
      ∀ p : HeightOneSpectrum (𝓞 K), p ∉ s →
        (normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)
            (algebraMap (𝓞 K) K f) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, one_ne_zero, ?_, ?_⟩ <;> simp
  | @insert q s hq ih =>
      obtain ⟨g, hg, hgs, hgother⟩ := ih
      obtain ⟨a, ha, haq, haother⟩ := NormFamily.exists_normalized_integral_isolated_prime q
      have hprod (p : HeightOneSpectrum (𝓞 K)) :
          (normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)
              (algebraMap (𝓞 K) K (a * g)) =
            (normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)
                (algebraMap (𝓞 K) K a) *
              (normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)
                (algebraMap (𝓞 K) K g) := by
        rw [map_mul, map_mul]
      have hout (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ insert q s) :
          (normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)
              (algebraMap (𝓞 K) K (a * g)) = 1 := by
        have hpq : p ≠ q := fun h => hp (by simp [h])
        have hps : p ∉ s := fun h => hp (Finset.mem_insert_of_mem h)
        rw [hprod, haother p hpq, hgother p hps, one_mul]
      refine ⟨a * g, mul_ne_zero ha hg, ?_, hout⟩
      intro p
      constructor
      · intro hp
        by_contra hnot
        rw [hout p hnot] at hp
        exact (lt_irrefl 1) hp
      · intro hp
        rcases Finset.mem_insert.mp hp with rfl | hps
        · rw [hprod]
          refine (mul_le_of_le_one_right
            (((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).nonneg _)
            ?_).trans_lt haq
          exact NumberField.abs_le_one_of_isIntegral (normalizedPrimeParameter_mem_fin p)
            (NumberField.RingOfIntegers.isIntegral_coe g)
        · by_cases hpq : p = q
          · subst p
            exact False.elim (hq hps)
          · rw [hprod, haother p hpq, one_mul]
            exact (hgs p).mpr hps

/-- The produced prime-place bijection transports prescribed finite support
to every actual source-normalized finite place. -/
theorem exists_normalized_integral_finitePlace_support
    (s : Finset (normalizedNumberFieldAdelicStructure K).Ωfin) :
    ∃ f : 𝓞 K, f ≠ 0 ∧
      (∀ ω : (normalizedNumberFieldAdelicStructure K).Ωfin,
        (normalizedNumberFieldAdelicStructure K).ϕ ω.1
            (algebraMap (𝓞 K) K f) < 1 ↔ ω ∈ s) ∧
      ∀ ω : (normalizedNumberFieldAdelicStructure K).Ωfin, ω ∉ s →
        (normalizedNumberFieldAdelicStructure K).ϕ ω.1
            (algebraMap (𝓞 K) K f) = 1 := by
  classical
  let e := normalizedPrimeEquivFinite (K := K)
  let t := s.image e.symm
  have hmem (ω : (normalizedNumberFieldAdelicStructure K).Ωfin) :
      e.symm ω ∈ t ↔ ω ∈ s := by
    constructor
    · intro hp
      obtain ⟨τ, hτ, hτp⟩ := Finset.mem_image.mp hp
      exact e.symm.injective hτp ▸ hτ
    · intro hω
      exact Finset.mem_image.mpr ⟨ω, hω, rfl⟩
  have hpoint (ω : (normalizedNumberFieldAdelicStructure K).Ωfin) :
      normalizedPrimeParameter (e.symm ω) = ω.1 :=
    congrArg Subtype.val (e.apply_symm_apply ω)
  obtain ⟨f, hf, hcontract, hone⟩ := exists_normalized_integral_prime_support t
  refine ⟨f, hf, ?_, ?_⟩
  · intro ω
    have h := hcontract (e.symm ω)
    rw [hpoint] at h
    exact h.trans (hmem ω)
  · intro ω hω
    have h := hone (e.symm ω) (fun hp => hω ((hmem ω).mp hp))
    rwa [hpoint] at h

/-- The literal source statement for an arbitrary finite subset of the actual
finite-place locus, rather than only a chosen list or finite test collection. -/
theorem exists_normalized_integral_support_of_finite
    (s : Set (normalizedNumberFieldAdelicStructure K).Ωfin) (hs : s.Finite) :
    ∃ f : 𝓞 K, f ≠ 0 ∧
      (∀ ω : (normalizedNumberFieldAdelicStructure K).Ωfin,
        (normalizedNumberFieldAdelicStructure K).ϕ ω.1
            (algebraMap (𝓞 K) K f) < 1 ↔ ω ∈ s) ∧
      ∀ ω : (normalizedNumberFieldAdelicStructure K).Ωfin, ω ∉ s →
        (normalizedNumberFieldAdelicStructure K).ϕ ω.1
            (algebraMap (𝓞 K) K f) = 1 := by
  obtain ⟨f, hf, hcontract, hone⟩ := exists_normalized_integral_finitePlace_support hs.toFinset
  refine ⟨f, hf, ?_, ?_⟩
  · intro ω
    exact (hcontract ω).trans hs.mem_toFinset
  · intro ω hω
    exact hone ω (fun hp => hω (hs.mem_toFinset.mp hp))

end ArakelovGeometry.ActualPrimeIndexing

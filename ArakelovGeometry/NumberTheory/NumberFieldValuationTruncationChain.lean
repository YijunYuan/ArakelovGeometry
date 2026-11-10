/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.ValuationModuleChain
import ArakelovGeometry.NumberTheory.ValuationModuleCriterion
import Mathlib.RingTheory.PicardGroup

/-!
# Actual normalized finite-place truncation chains

The accepted genuine prime-indexed construction is transported to the
actual normalized finite places. Its literal finitely generated stages
are actual fractional ideals; finite negative support makes each stage
nonzero and tensor-invertible. No prime-power factorization or localization
formula is asserted here.
-/

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Pointwise

noncomputable section

namespace ArakelovGeometry.FiniteValuation

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]

attribute [local instance 2000] Algebra.toModule

/-- The source truncation on the actual normalized finite places. -/
def normalizedPositiveTruncation
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (s : Finset (normalizedNumberFieldAdelicStructure K).Ωfin)
    (ω : (normalizedNumberFieldAdelicStructure K).Ωfin) : ℤ := by
  classical
  exact if ω ∈ s then b ω else min (b ω) 0

theorem normalizedPositiveTruncation_map
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 K))) (p : HeightOneSpectrum (𝓞 K)) :
    normalizedPositiveTruncation b (s.map normalizedPrimeEquivFinite.toEmbedding)
      (normalizedPrimeEquivFinite p) =
      positiveTruncation (fun q => b (normalizedPrimeEquivFinite q)) s p := by
  classical
  simp [normalizedPositiveTruncation, positiveTruncation]

theorem normalizedPositiveTruncation_pullback
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (s : Finset (normalizedNumberFieldAdelicStructure K).Ωfin)
    (p : HeightOneSpectrum (𝓞 K)) :
    normalizedPositiveTruncation b s (normalizedPrimeEquivFinite p) =
      positiveTruncation (fun q => b (normalizedPrimeEquivFinite q))
        (s.map normalizedPrimeEquivFinite.symm.toEmbedding) p := by
  classical
  simp [normalizedPositiveTruncation, positiveTruncation]

theorem normalizedPositiveTruncation_negative_iff
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (s : Finset (normalizedNumberFieldAdelicStructure K).Ωfin)
    (ω : (normalizedNumberFieldAdelicStructure K).Ωfin) :
    normalizedPositiveTruncation b s ω < 0 ↔ b ω < 0 := by
  classical
  by_cases h : ω ∈ s <;> simp [normalizedPositiveTruncation, h]

theorem finite_positive_normalizedPositiveTruncation
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (s : Finset (normalizedNumberFieldAdelicStructure K).Ωfin) :
    {p | 0 < normalizedPositiveTruncation b s (normalizedPrimeEquivFinite p)}.Finite := by
  classical
  apply (s.finite_toSet.preimage normalizedPrimeEquivFinite.injective.injOn).subset
  intro p hp
  by_contra hs
  change normalizedPrimeEquivFinite p ∉ s at hs
  simp [normalizedPositiveTruncation, hs] at hp

theorem fg_normalizedPositiveTruncation_valuationModule
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (s : Finset (normalizedNumberFieldAdelicStructure K).Ωfin) :
    (valuationModule (K := K)
      (fun p => normalizedPositiveTruncation b s (normalizedPrimeEquivFinite p))).FG :=
  fg_valuationModule_of_finite_positive (finite_positive_normalizedPositiveTruncation b s)

/-- The actual fractional ideal has exactly the literal truncation module. -/
def normalizedTruncationFractionalIdeal
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (s : Finset (normalizedNumberFieldAdelicStructure K).Ωfin) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  ⟨valuationModule (K := K)
      (fun p => normalizedPositiveTruncation b s (normalizedPrimeEquivFinite p)),
    FractionalIdeal.isFractional_of_fg (fg_normalizedPositiveTruncation_valuationModule b s)⟩

@[simp]
theorem normalizedTruncationFractionalIdeal_coe
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (s : Finset (normalizedNumberFieldAdelicStructure K).Ωfin) :
    (normalizedTruncationFractionalIdeal b s : Submodule (𝓞 K) K) =
      valuationModule (K := K)
        (fun p => normalizedPositiveTruncation b s (normalizedPrimeEquivFinite p)) := rfl

theorem normalizedTruncationFractionalIdeal_ne_zero
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (hneg : {ω | b ω < 0}.Finite)
    (s : Finset (normalizedNumberFieldAdelicStructure K).Ωfin) :
    normalizedTruncationFractionalIdeal b s ≠ 0 := by
  have hpull : {p | b (normalizedPrimeEquivFinite p) < 0}.Finite :=
    hneg.preimage (f := normalizedPrimeEquivFinite (K := K))
      normalizedPrimeEquivFinite.injective.injOn
  obtain ⟨a, ha, hamem⟩ := exists_ring_mem_valuationModule_of_finite_negative (K := K) hpull
  have hamem' : algebraMap (𝓞 K) K a ∈
      (normalizedTruncationFractionalIdeal b s : Submodule (𝓞 K) K) := by
    simp only [normalizedTruncationFractionalIdeal_coe, mem_valuationModule_iff,
      normalizedPositiveTruncation_pullback]
    exact ring_mem_valuationModule_positiveTruncation hamem _
  intro hzero
  have hbot := FractionalIdeal.coeToSubmodule_eq_bot.mpr hzero
  rw [hbot] at hamem'
  have h := (Submodule.mem_bot (𝓞 K)).mp hamem'
  exact ha ((IsFractionRing.injective (𝓞 K) K) (by simpa only [map_zero] using h))

/-- A genuine fractional-ideal tensor inverse supplies module invertibility. -/
theorem fractionalIdeal_module_invertible
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) :
    Module.Invertible (𝓞 K) (J : Submodule (𝓞 K) K) := by
  have hmul : (J : Submodule (𝓞 K) K) *
      ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) = 1 := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one]
  let U : (Submodule (𝓞 K) K)ˣ :=
    ⟨J, ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K),
      hmul, by simpa only [mul_comm] using hmul⟩
  exact Module.Invertible.left (Submodule.tensorInvEquiv U)

theorem normalizedTruncationFractionalIdeal_invertible
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (hneg : {ω | b ω < 0}.Finite)
    (s : Finset (normalizedNumberFieldAdelicStructure K).Ωfin) :
    Module.Invertible (𝓞 K)
      (normalizedTruncationFractionalIdeal b s : Submodule (𝓞 K) K) :=
  fractionalIdeal_module_invertible _ (normalizedTruncationFractionalIdeal_ne_zero b hneg s)


/-- The genuine source chain at the literal normalized finite places. -/
theorem exists_normalizedFinitePlace_strictMono_positiveTruncation
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (hneg : {ω | b ω < 0}.Finite) (hpos : {ω | 0 < b ω}.Infinite) :
    ∃ s : ℕ → Finset (normalizedNumberFieldAdelicStructure K).Ωfin,
      StrictMono (fun n => valuationModule (K := K)
        (fun p => normalizedPositiveTruncation b (s n) (normalizedPrimeEquivFinite p))) ∧
      (∀ n, (valuationModule (K := K)
        (fun p => normalizedPositiveTruncation b (s n) (normalizedPrimeEquivFinite p))).FG) ∧
      (∀ n, valuationModule (K := K)
        (fun p => normalizedPositiveTruncation b (s n) (normalizedPrimeEquivFinite p)) ≠ ⊥) ∧
      (⨆ n, valuationModule (K := K)
        (fun p => normalizedPositiveTruncation b (s n) (normalizedPrimeEquivFinite p))) =
        valuationModule (K := K) (fun p => b (normalizedPrimeEquivFinite p)) ∧
      ∀ x : K, x ∈ valuationModule (K := K) (fun p => b (normalizedPrimeEquivFinite p)) ↔
        ∃ n, x ∈ valuationModule (K := K)
          (fun p => normalizedPositiveTruncation b (s n) (normalizedPrimeEquivFinite p)) := by
  classical
  have hn : {p | b (normalizedPrimeEquivFinite p) < 0}.Finite :=
    hneg.preimage (f := normalizedPrimeEquivFinite (K := K))
      normalizedPrimeEquivFinite.injective.injOn
  have hp : {p | 0 < b (normalizedPrimeEquivFinite p)}.Infinite := by
    intro h
    exact hpos (Set.Finite.of_preimage (f := normalizedPrimeEquivFinite (K := K))
      (s := {ω | 0 < b ω}) h normalizedPrimeEquivFinite.surjective)
  obtain ⟨s, hstrict, hfg, hne, hsup, hmem⟩ :=
    exists_numberField_strictMono_valuationModule_positiveTruncation K hn hp
  let t : ℕ → Finset (normalizedNumberFieldAdelicStructure K).Ωfin :=
    fun n => (s n).map normalizedPrimeEquivFinite.toEmbedding
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [t, normalizedPositiveTruncation_map] using hstrict
  · simpa only [t, normalizedPositiveTruncation_map] using hfg
  · simpa only [t, normalizedPositiveTruncation_map] using hne
  · simpa only [t, normalizedPositiveTruncation_map] using hsup
  · simpa only [t, normalizedPositiveTruncation_map] using hmem

/-- The same literal chain consists of genuine nonzero invertible
fractional ideals, rather than auxiliary module certificates. -/
theorem exists_normalizedFinitePlace_fractionalIdeal_truncation_chain
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (hneg : {ω | b ω < 0}.Finite) (hpos : {ω | 0 < b ω}.Infinite) :
    ∃ s : ℕ → Finset (normalizedNumberFieldAdelicStructure K).Ωfin,
      StrictMono (fun n => normalizedTruncationFractionalIdeal b (s n)) ∧
      (∀ n, (normalizedTruncationFractionalIdeal b (s n) : Submodule (𝓞 K) K).FG) ∧
      (∀ n, normalizedTruncationFractionalIdeal b (s n) ≠ 0) ∧
      (∀ n, Module.Invertible (𝓞 K)
        (normalizedTruncationFractionalIdeal b (s n) : Submodule (𝓞 K) K)) ∧
      (⨆ n, (normalizedTruncationFractionalIdeal b (s n) : Submodule (𝓞 K) K)) =
        valuationModule (K := K) (fun p => b (normalizedPrimeEquivFinite p)) ∧
      ∀ x : K, x ∈ valuationModule (K := K) (fun p => b (normalizedPrimeEquivFinite p)) ↔
        ∃ n, x ∈ normalizedTruncationFractionalIdeal b (s n) := by
  obtain ⟨s, hstrict, hfg, _, hsup, hmem⟩ :=
    exists_normalizedFinitePlace_strictMono_positiveTruncation b hneg hpos
  refine ⟨s, ?_, ?_, fun n => normalizedTruncationFractionalIdeal_ne_zero b hneg (s n),
    fun n => normalizedTruncationFractionalIdeal_invertible b hneg (s n), ?_, ?_⟩
  · intro i j hij
    change (valuationModule (K := K)
      (fun p => normalizedPositiveTruncation b (s i) (normalizedPrimeEquivFinite p))) <
        valuationModule (K := K)
          (fun p => normalizedPositiveTruncation b (s j) (normalizedPrimeEquivFinite p))
    exact hstrict hij
  · simpa only [normalizedTruncationFractionalIdeal_coe] using hfg
  · simpa only [normalizedTruncationFractionalIdeal_coe] using hsup
  · exact hmem

/-- The actual strict chain supplies the source non-finite-generation
conclusion through finite-generator stabilization. -/
theorem not_fg_normalizedFinitePlace_valuationModule_of_truncation_chain
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (hneg : {ω | b ω < 0}.Finite) (hpos : {ω | 0 < b ω}.Infinite) :
    ¬ (valuationModule (K := K) (fun p => b (normalizedPrimeEquivFinite p))).FG := by
  obtain ⟨s, hstrict, _, _, _, hsup, _⟩ :=
    exists_normalizedFinitePlace_fractionalIdeal_truncation_chain b hneg hpos
  let C : ℕ →o Submodule (𝓞 K) K :=
    ⟨fun n => normalizedTruncationFractionalIdeal b (s n), fun i j hij =>
      FractionalIdeal.coe_le_coe.mpr (hstrict.monotone hij)⟩
  intro hfg
  obtain ⟨n, hn⟩ := hfg.stabilizes_of_iSup_eq C hsup
  have hnext : C (n + 1) ≤ valuationModule (K := K)
      (fun p => b (normalizedPrimeEquivFinite p)) := by
    rw [← hsup]
    exact le_iSup (fun k => (normalizedTruncationFractionalIdeal b (s k) : Submodule (𝓞 K) K)) _
  rw [hn] at hnext
  have hlt : C n < C (n + 1) := by
    exact hstrict (Nat.lt_succ_self n)
  exact not_le_of_gt hlt hnext

end ArakelovGeometry.FiniteValuation

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.PrimePole
public import Mathlib.Data.Rat.Encodable
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.Basic.Denumerable
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Finite positive truncations of actual prime-valuation modules

Finite positive truncations form a directed exhaustion for any Dedekind domain.
An infinite positive support and a finite negative support produce strict
extensions; with a countable height-one spectrum they yield an actual strictly
ascending sequence with the full valuation module as its union.

Reference: Chen–Moriwaki, Lemma 4.4.7, PDF page 309.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.FiniteValuation

open IsDedekindDomain
open scoped WithZero

variable {R : Type*} [CommRing R]

/-- Keep all nonpositive bounds and the positive bounds on the given finite set. -/
def positiveTruncation (b : HeightOneSpectrum R → ℤ) (s : Finset (HeightOneSpectrum R))
    (v : HeightOneSpectrum R) : ℤ := by
  classical
  exact if v ∈ s then b v else min (b v) 0

/-- A finite positive truncation lies below the original family of bounds. -/
theorem positiveTruncation_le (b : HeightOneSpectrum R → ℤ)
    (s : Finset (HeightOneSpectrum R)) : positiveTruncation b s ≤ b := by
  classical
  intro v
  by_cases hv : v ∈ s
  · simp [positiveTruncation, hv]
  · simp only [positiveTruncation, hv, ↓reduceIte]
    exact min_le_left _ _

/-- Enlarging the finite set increases the positive truncation. -/
theorem positiveTruncation_mono (b : HeightOneSpectrum R → ℤ)
    {s t : Finset (HeightOneSpectrum R)} (hst : s ⊆ t) :
    positiveTruncation b s ≤ positiveTruncation b t := by
  classical
  intro v
  by_cases hs : v ∈ s
  · simp [positiveTruncation, hs, hst hs]
  · by_cases ht : v ∈ t
    · simp only [positiveTruncation, hs, ht, ↓reduceIte]
      exact min_le_left _ _
    · simp [positiveTruncation, hs, ht]

/-- A finite positive truncation has finite positive support. -/
theorem finite_positive_positiveTruncation (b : HeightOneSpectrum R → ℤ)
    (s : Finset (HeightOneSpectrum R)) : {v | 0 < positiveTruncation b s v}.Finite := by
  classical
  apply s.finite_toSet.subset
  intro v hv
  by_contra hvs
  change v ∉ s at hvs
  simp [positiveTruncation, hvs] at hv

variable [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every actual finite positive truncation is finitely generated. -/
theorem fg_valuationModule_positiveTruncation (b : HeightOneSpectrum R → ℤ)
    (s : Finset (HeightOneSpectrum R)) :
    (valuationModule (K := K) (positiveTruncation b s)).FG := by
  exact fg_valuationModule_of_finite_positive (finite_positive_positiveTruncation b s)

/-- Every actual module element belongs to some finite positive truncation. -/
theorem exists_mem_valuationModule_positiveTruncation {b : HeightOneSpectrum R → ℤ}
    {x : K} (hx : x ∈ valuationModule (K := K) b) :
    ∃ s : Finset (HeightOneSpectrum R),
      x ∈ valuationModule (K := K) (positiveTruncation b s) := by
  classical
  by_cases hx0 : x = 0
  · exact ⟨∅, hx0 ▸ Submodule.zero_mem _⟩
  let hs := finite_valuation_ne_one (R := R) hx0
  refine ⟨hs.toFinset, ?_⟩
  intro v
  by_cases hv : v ∈ hs.toFinset
  · simpa only [positiveTruncation, hv, ↓reduceIte] using hx v
  · have hv1 : v.valuation K x = 1 := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv
    have hb : 0 ≤ b v := by
      have h := hx v
      rw [hv1, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
      exact h
    simp only [positiveTruncation, hv, ↓reduceIte, min_eq_right hb,
      WithZero.exp_zero, hv1, le_refl]

/-- The actual finite positive truncations form a directed family of submodules. -/
theorem directed_valuationModule_positiveTruncation (b : HeightOneSpectrum R → ℤ) :
    Directed (· ≤ ·) (fun s : Finset (HeightOneSpectrum R) =>
      valuationModule (K := K) (positiveTruncation b s)) := by
  classical
  intro s t
  refine ⟨s ∪ t, ?_, ?_⟩
  · exact valuationModule_mono (positiveTruncation_mono b Finset.subset_union_left)
  · exact valuationModule_mono (positiveTruncation_mono b Finset.subset_union_right)

/-- The supremum of actual finite positive truncations is the original module. -/
theorem iSup_valuationModule_positiveTruncation (b : HeightOneSpectrum R → ℤ) :
    (⨆ s : Finset (HeightOneSpectrum R),
      valuationModule (K := K) (positiveTruncation b s)) = valuationModule (K := K) b := by
  apply le_antisymm
  · exact iSup_le fun s => valuationModule_mono (positiveTruncation_le b s)
  · intro x hx
    obtain ⟨s, hs⟩ := exists_mem_valuationModule_positiveTruncation hx
    exact Submodule.mem_iSup_of_mem s hs

/-- A prime insertion is strict when a ring member has unit valuation at the new prime. -/
theorem valuationModule_positiveTruncation_lt_insert_of_ring_member
    {b : HeightOneSpectrum R → ℤ} {s : Finset (HeightOneSpectrum R)} {a : R}
    (ha : algebraMap R K a ∈ valuationModule (K := K) (positiveTruncation b s))
    {p : HeightOneSpectrum R} (hp : p ∉ s) (hbp : 0 < b p)
    (hap : p.valuation K (algebraMap R K a) = 1) :
    valuationModule (K := K) (positiveTruncation b s) <
      valuationModule (K := K) (positiveTruncation b (Finset.cons p s hp)) := by
  classical
  rw [Finset.cons_eq_insert]
  have hle := valuationModule_mono
    (positiveTruncation_mono b (Finset.subset_insert p s)) (K := K)
  refine lt_iff_le_not_ge.mpr ⟨hle, ?_⟩
  intro hback
  have hbp' : 0 < positiveTruncation b (insert p s) p := by
    simpa [positiveTruncation] using hbp
  obtain ⟨x, hx, hxp⟩ := exists_valuationModule_pole_of_ring_member (hle ha) p hbp' hap
  have hbound := hback hx p
  have hzero : positiveTruncation b s p = 0 := by
    simp [positiveTruncation, hp, min_eq_right (le_of_lt hbp)]
  rw [hzero, WithZero.exp_zero] at hbound
  exact not_lt_of_ge hbound hxp

/-- Original-ring members of the actual module survive every positive truncation. -/
theorem ring_mem_valuationModule_positiveTruncation {b : HeightOneSpectrum R → ℤ}
    {a : R} (ha : algebraMap R K a ∈ valuationModule (K := K) b)
    (s : Finset (HeightOneSpectrum R)) :
    algebraMap R K a ∈ valuationModule (K := K) (positiveTruncation b s) := by
  classical
  intro v
  by_cases hv : v ∈ s
  · simpa [positiveTruncation, hv] using ha v
  · by_cases hb : b v ≤ 0
    · simpa [positiveTruncation, hv, min_eq_left hb] using ha v
    · simpa [positiveTruncation, hv, min_eq_right (le_of_not_ge hb)] using
        v.valuation_le_one (K := K) a

/-- A monotone sequence covering the positive support exhausts the actual module. -/
theorem exists_mem_valuationModule_positiveTruncation_of_cofinal
    {b : HeightOneSpectrum R → ℤ} (s : ℕ → Finset (HeightOneSpectrum R))
    (hs : Monotone s) (hcover : ∀ p, 0 < b p → ∃ n, p ∈ s n)
    {x : K} (hx : x ∈ valuationModule (K := K) b) :
    ∃ n, x ∈ valuationModule (K := K) (positiveTruncation b (s n)) := by
  classical
  have hfinite (t : Finset (HeightOneSpectrum R)) :
      ∃ n, ∀ p ∈ t, 0 < b p → p ∈ s n := by
    induction t using Finset.induction with
    | empty => exact ⟨0, by simp⟩
    | @insert p t _ ih =>
      obtain ⟨n, hn⟩ := ih
      by_cases hp : 0 < b p
      · obtain ⟨m, hm⟩ := hcover p hp
        refine ⟨max n m, ?_⟩
        intro q hq hpos
        rcases Finset.mem_insert.mp hq with rfl | hqt
        · exact hs (le_max_right n m) hm
        · exact hs (le_max_left n m) (hn q hqt hpos)
      · refine ⟨n, ?_⟩
        intro q hq hpos
        rcases Finset.mem_insert.mp hq with rfl | hqt
        · exact False.elim (hp hpos)
        · exact hn q hqt hpos
  obtain ⟨t, ht⟩ := exists_mem_valuationModule_positiveTruncation hx
  obtain ⟨n, hn⟩ := hfinite t
  refine ⟨n, valuationModule_mono (b := positiveTruncation b t) ?_ ht⟩
  intro p
  by_cases hpt : p ∈ t
  · by_cases hp : 0 < b p
    · simp [positiveTruncation, hpt, hn p hpt hp]
    · simp [positiveTruncation, hpt, min_eq_left (le_of_not_gt hp)]
  · by_cases hps : p ∈ s n
    · simp only [positiveTruncation, hpt, hps, ↓reduceIte]
      exact min_le_left _ _
    · simp [positiveTruncation, hpt, hps]

/-- A countable Dedekind domain has a countable height-one spectrum. -/
theorem countable_heightOneSpectrum_of_countable [Countable R] :
    Countable (HeightOneSpectrum R) := by
  classical
  have hsurj : Function.Surjective
      (fun s : Finset R => Ideal.span (s : Set R)) := by
    intro I
    obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing I
    exact ⟨s, hs⟩
  let : Countable (Ideal R) := hsurj.countable
  exact HeightOneSpectrum.asIdeal_injective.countable

/-- Countability and the arithmetic support hypotheses produce an actual strict FG chain. -/
theorem exists_strictMono_valuationModule_positiveTruncation
    [Countable (HeightOneSpectrum R)] {b : HeightOneSpectrum R → ℤ}
    (hneg : {p | b p < 0}.Finite) (hpos : {p | 0 < b p}.Infinite) :
    ∃ s : ℕ → Finset (HeightOneSpectrum R),
      StrictMono (fun n => valuationModule (K := K) (positiveTruncation b (s n))) ∧
      (∀ n, (valuationModule (K := K) (positiveTruncation b (s n))).FG) ∧
      (∀ n, valuationModule (K := K) (positiveTruncation b (s n)) ≠ ⊥) ∧
      (⨆ n, valuationModule (K := K) (positiveTruncation b (s n))) =
        valuationModule (K := K) b ∧
      ∀ x : K, x ∈ valuationModule (K := K) b ↔
        ∃ n, x ∈ valuationModule (K := K) (positiveTruncation b (s n)) := by
  classical
  obtain ⟨a, ha, hamem⟩ := exists_ring_mem_valuationModule_of_finite_negative (K := K) hneg
  have haK : algebraMap R K a ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne ha
  let E := {p : HeightOneSpectrum R | p.valuation K (algebraMap R K a) ≠ 1}
  have hE : E.Finite := finite_valuation_ne_one (R := R) haK
  let S := {p : HeightOneSpectrum R | 0 < b p} \ E
  have hS : S.Infinite := hpos.sdiff hE
  let : Infinite S := hS.to_subtype
  obtain ⟨e⟩ := (inferInstance : Nonempty (ℕ ≃ S))
  let f : ℕ → HeightOneSpectrum R := fun n => (e n).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let s : ℕ → Finset (HeightOneSpectrum R) :=
    fun n => hE.toFinset ∪ (Finset.range n).image f
  have hs : Monotone s := by
    intro n m hnm p hp
    rcases Finset.mem_union.mp hp with hpE | hpimage
    · exact Finset.mem_union.mpr (Or.inl hpE)
    · obtain ⟨j, hj, hfj⟩ := Finset.mem_image.mp hpimage
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨j, Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hnm), hfj⟩))
  have hnot (n : ℕ) : f n ∉ s n := by
    intro hn
    rcases Finset.mem_union.mp hn with hnE | hnimage
    · exact (e n).property.2 (hE.mem_toFinset.mp hnE)
    · obtain ⟨j, hj, hfj⟩ := Finset.mem_image.mp hnimage
      have hjn : j = n := hf hfj
      subst j
      exact Nat.lt_irrefl n (Finset.mem_range.mp hj)
  have hsucc (n : ℕ) : s (n + 1) = insert (f n) (s n) := by
    simp only [s, Finset.range_add_one, Finset.image_insert, Finset.union_insert]
  have hstrict : StrictMono (fun n =>
      valuationModule (K := K) (positiveTruncation b (s n))) := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hsucc n]
    have hap : (f n).valuation K (algebraMap R K a) = 1 := by
      exact not_not.mp (e n).property.2
    simpa only [Finset.cons_eq_insert] using
      valuationModule_positiveTruncation_lt_insert_of_ring_member
        (ring_mem_valuationModule_positiveTruncation hamem (s n)) (hnot n)
        (e n).property.1 hap
  have hcover : ∀ p, 0 < b p → ∃ n, p ∈ s n := by
    intro p hp
    by_cases hpE : p ∈ E
    · exact ⟨0, Finset.mem_union.mpr (Or.inl (hE.mem_toFinset.mpr hpE))⟩
    · let q : S := ⟨p, hp, hpE⟩
      refine ⟨e.symm q + 1, Finset.mem_union.mpr (Or.inr ?_)⟩
      refine Finset.mem_image.mpr ⟨e.symm q, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply q)
  have hexhaust (x : K) (hx : x ∈ valuationModule (K := K) b) :
      ∃ n, x ∈ valuationModule (K := K) (positiveTruncation b (s n)) :=
    exists_mem_valuationModule_positiveTruncation_of_cofinal s hs hcover hx
  refine ⟨s, hstrict, fun n => fg_valuationModule_positiveTruncation b (s n), ?_, ?_, ?_⟩
  · intro n hzero
    apply haK
    have hmem := ring_mem_valuationModule_positiveTruncation hamem (s n)
    rw [hzero] at hmem
    exact (Submodule.mem_bot R).mp hmem
  · apply le_antisymm
    · exact iSup_le fun n => valuationModule_mono (positiveTruncation_le b (s n))
    · intro x hx
      obtain ⟨n, hn⟩ := hexhaust x hx
      exact Submodule.mem_iSup_of_mem n hn
  · intro x
    refine ⟨hexhaust x, ?_⟩
    rintro ⟨n, hn⟩
    exact valuationModule_mono (positiveTruncation_le b (s n)) hn

/-- The actual prime spectrum of the ring of integers of a number field is countable. -/
theorem countable_numberField_heightOneSpectrum (F : Type*) [Field F] [NumberField F] :
    Countable (HeightOneSpectrum (NumberField.RingOfIntegers F)) := by
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (NumberField.RingOfIntegers F) := Subtype.val_injective.countable
  exact countable_heightOneSpectrum_of_countable

/-- The source's actual strict truncation chain is produced over every number field. -/
theorem exists_numberField_strictMono_valuationModule_positiveTruncation
    (F : Type*) [Field F] [NumberField F]
    {b : HeightOneSpectrum (NumberField.RingOfIntegers F) → ℤ}
    (hneg : {p | b p < 0}.Finite) (hpos : {p | 0 < b p}.Infinite) :
    ∃ s : ℕ → Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)),
      StrictMono (fun n => valuationModule (K := F) (positiveTruncation b (s n))) ∧
      (∀ n, (valuationModule (K := F) (positiveTruncation b (s n))).FG) ∧
      (∀ n, valuationModule (K := F) (positiveTruncation b (s n)) ≠ ⊥) ∧
      (⨆ n, valuationModule (K := F) (positiveTruncation b (s n))) =
        valuationModule (K := F) b ∧
      ∀ x : F, x ∈ valuationModule (K := F) b ↔
        ∃ n, x ∈ valuationModule (K := F) (positiveTruncation b (s n)) := by
  let := countable_numberField_heightOneSpectrum F
  exact exists_strictMono_valuationModule_positiveTruncation hneg hpos

end ArakelovGeometry.FiniteValuation

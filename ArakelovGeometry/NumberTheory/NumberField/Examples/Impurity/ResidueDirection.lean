/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.PrimeIndexing
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.ProductFormulaComparison

/-!
# Fresh actual rational primes and residue directions

Choose genuine places on the normalized rational number-field curve, with
unit slopes avoiding any prescribed finite set of rational plane directions.
The diagonal sequence is used by the dominated infinite-distance family.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ArakelovGeometry.NumberFieldResidueDirection

open AdelicStructure ActualPrimeIndexing

abbrev S := normalizedNumberFieldAdelicStructure ℚ
abbrev Plane := ℚ × ℚ

/-- Actual rational primes give distinct actual normalized finite places. -/
def primePoint (p : Nat.Primes) : S.Ω :=
  normalizedPrimeParameter ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)

theorem primePoint_injective : Function.Injective primePoint :=
  normalizedPrimeParameter_injective.comp
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective

theorem primePoint_mem_fin (p : Nat.Primes) : primePoint p ∈ S.Ωfin :=
  normalizedPrimeParameter_mem_fin _

/-- Finite sets of nonzero rational scalars are units outside finitely many places. -/
theorem exists_finite_exceptional_units (A : Finset ℚ) :
    ∃ T : Finset S.Ω, ∀ ω, ω ∉ T → ∀ a ∈ A, a ≠ 0 → S.ϕ ω a = 1 := by
  classical
  have hA : ∀ a ∈ (A : Set ℚ), ({ω : S.Ω | S.ϕ ω a ≠ 1} \ {ω | a = 0}).Finite := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · exact (normalizedPlaceValue_hasFiniteMulSupport ha).subset (fun _ h ↦ h.1)
  have hfin := A.finite_toSet.biUnion hA
  refine ⟨hfin.toFinset, ?_⟩
  intro ω hω a ha ha0
  by_contra hne
  apply hω
  rw [hfin.mem_toFinset]
  exact Set.mem_biUnion ha ⟨hne, ha0⟩

/-- A fresh actual finite place and a unit slope avoid every vector in a finite list. -/
theorem exists_fresh_place_slope (T : Finset S.Ω) (A : Finset Plane) :
    ∃ (ω : S.Ω) (a : ℚ), ω ∉ T ∧ ω ∈ S.Ωfin ∧ S.ϕ ω a = 1 ∧
      ∀ z ∈ A, S.ϕ ω (z.2 - a * z.1) = max (S.ϕ ω z.1) (S.ϕ ω z.2) := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (insert 0 (A.image fun z ↦ z.2 / z.1))
  have ha0 : a ≠ 0 := fun h ↦ ha (by simp [h])
  have hslope : ∀ z ∈ A, z ≠ 0 → z.2 - a * z.1 ≠ 0 := by
    intro z hz hz0 heq
    have hz1 : z.1 ≠ 0 := by
      intro hx
      have hy : z.2 = 0 := by simpa [hx] using heq
      exact hz0 (Prod.ext hx hy)
    have he : a = z.2 / z.1 := (eq_div_iff hz1).mpr (sub_eq_zero.mp heq).symm
    exact ha (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z, hz, he.symm⟩))
  let B : Finset ℚ := insert a ((A.image Prod.fst ∪ A.image Prod.snd) ∪
    A.image fun z ↦ z.2 - a * z.1)
  obtain ⟨U, hU⟩ := exists_finite_exceptional_units B
  have hpre : (primePoint ⁻¹' ((T ∪ U : Finset S.Ω) : Set S.Ω)).Finite :=
    (T ∪ U).finite_toSet.preimage primePoint_injective.injOn
  obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset hpre.toFinset
  have hnot : primePoint p ∉ T ∪ U := by
    simpa only [hpre.mem_toFinset, Set.mem_preimage, Finset.mem_coe] using hp
  have hT : primePoint p ∉ T := fun h ↦ hnot (Finset.mem_union_left _ h)
  have hUU : primePoint p ∉ U := fun h ↦ hnot (Finset.mem_union_right _ h)
  have hunit := hU (primePoint p) hUU
  refine ⟨primePoint p, a, hT, primePoint_mem_fin p, hunit a (by simp [B]) ha0, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  · rw [hunit _ (by
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)))
      (hslope z hz hz0)]
    have hx : S.ϕ (primePoint p) z.1 = if z.1 = 0 then 0 else 1 := by
      split_ifs with h
      · simp [h]
      · exact hunit _ (by
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)))) h
    have hy : S.ϕ (primePoint p) z.2 = if z.2 = 0 then 0 else 1 := by
      split_ifs with h
      · simp [h]
      · exact hunit _ (by
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)))) h
    rw [hx, hy]
    split_ifs with h₁ h₂
    · exact False.elim (hz0 (Prod.ext h₁ h₂))
    all_goals norm_num

/-- The first rational vectors in the chosen encoding, used in the diagonal construction. -/
def tests (n : ℕ) : Finset Plane :=
  (Finset.range n).image fun k ↦ (Encodable.decode (α := Plane) k).getD 0

private theorem mem_tests (z : Plane) {n : ℕ} (hn : Encodable.encode z < n) : z ∈ tests n := by
  apply Finset.mem_image.mpr
  exact ⟨Encodable.encode z, Finset.mem_range.mpr hn, by simp⟩

/-- Choose a new finite place and a unit slope avoiding finitely many rational directions. -/
theorem exists_choice (n : ℕ) (T : Finset S.Ω) :
    ∃ q : S.Ω × ℚ, q.1 ∉ T ∧ q.1 ∈ S.Ωfin ∧ S.ϕ q.1 q.2 = 1 ∧
      ∀ z ∈ tests n, S.ϕ q.1 (z.2 - q.2 * z.1) = max (S.ϕ q.1 z.1) (S.ϕ q.1 z.2) := by
  obtain ⟨ω, a, h⟩ := exists_fresh_place_slope T (tests n)
  exact ⟨(ω, a), h⟩

/-- A place and slope avoiding the first test vectors and all previously selected places. -/
def choice (n : ℕ) (T : Finset S.Ω) : S.Ω × ℚ := (exists_choice n T).choose

open Classical in
/-- The finite set of places selected before a given step of the diagonal construction. -/
def used : ℕ → Finset S.Ω
  | 0 => ∅
  | n + 1 => insert (choice n (used n)).1 (used n)

/-- The pairwise distinct actual finite places selected by the arithmetic diagonal argument. -/
def point (n : ℕ) : S.Ω := (choice n (used n)).1

/-- The actual rational unit slope chosen at each diagonal place. -/
def slope (n : ℕ) : ℚ := (choice n (used n)).2

private theorem point_notMem_used (n : ℕ) : point n ∉ used n :=
  (exists_choice n (used n)).choose_spec.1

theorem point_mem_fin (n : ℕ) : point n ∈ S.Ωfin :=
  (exists_choice n (used n)).choose_spec.2.1

theorem slope_unit (n : ℕ) : S.ϕ (point n) (slope n) = 1 :=
  (exists_choice n (used n)).choose_spec.2.2.1

private theorem used_subset {n m : ℕ} (h : n ≤ m) : used n ⊆ used m := by
  classical
  induction m, h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ m h ih => exact ih.trans (Finset.subset_insert _ _)

private theorem point_mem_used {n m : ℕ} (h : n < m) : point n ∈ used m := by
  classical
  exact used_subset h (Finset.mem_insert_self _ _)

/-- No actual finite place is selected twice. -/
theorem point_injective : Function.Injective point := by
  intro n m h
  rcases lt_trichotomy n m with hnm | rfl | hmn
  · exact False.elim (point_notMem_used m (h ▸ point_mem_used hnm))
  · rfl
  · exact False.elim (point_notMem_used n (h.symm ▸ point_mem_used hmn))

/-- Each fixed rational vector avoids the expensive direction at every sufficiently late place. -/
theorem slope_avoids (z : Plane) {n : ℕ} (hn : Encodable.encode z < n) :
    S.ϕ (point n) (z.2 - slope n * z.1) =
      max (S.ϕ (point n) z.1) (S.ϕ (point n) z.2) :=
  (exists_choice n (used n)).choose_spec.2.2.2 z (mem_tests z hn)

/-- The places where a fixed rational vector can meet the expensive direction form a finite set. -/
theorem finite_expensive_places (z : Plane) :
    {ω : S.Ω | ∃ n, point n = ω ∧
      S.ϕ ω (z.2 - slope n * z.1) < max (S.ϕ ω z.1) (S.ϕ ω z.2)}.Finite := by
  apply ((Finset.range (Encodable.encode z + 1)).finite_toSet.image point).subset
  rintro ω ⟨n, rfl, hn⟩
  refine ⟨n, ?_, rfl⟩
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have he := slope_avoids z (by omega : Encodable.encode z < n)
  exact (ne_of_lt hn) he

end ArakelovGeometry.NumberFieldResidueDirection

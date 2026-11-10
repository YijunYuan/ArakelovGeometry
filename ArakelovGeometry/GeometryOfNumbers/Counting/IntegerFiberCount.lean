/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Counting actual integer points in a translated real interval -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.IntegerFiberCount

/-- The literal integer points of an arbitrary translated bounded interval form a finite set. -/
theorem finite_integer_fiber (a b x : ℝ) :
    {k : ℤ | a ≤ (k : ℝ) + x ∧ (k : ℝ) + x ≤ b}.Finite := by
  apply (Set.finite_Icc ⌈a - x⌉ ⌊b - x⌋).subset
  intro k hk
  apply Set.mem_Icc.mpr
  rw [Int.ceil_le, Int.le_floor]
  constructor <;> linarith [hk.1, hk.2]

/-- Translating the actual integer fibre does not change its unit spacing. -/
theorem card_le_length_add_one (s : Finset ℤ) {a b x : ℝ} (hab : a ≤ b)
    (hs : ∀ k ∈ s, a ≤ (k : ℝ) + x ∧ (k : ℝ) + x ≤ b) :
    (s.card : ℝ) ≤ b - a + 1 := by
  classical
  by_cases hne : s.Nonempty
  · let p := s.min' hne
    let q := s.max' hne
    have hp : p ∈ s := s.min'_mem hne
    have hq : q ∈ s := s.max'_mem hne
    have hpq : p ≤ q := s.min'_le q hq
    have hsub : s ⊆ Finset.Icc p q := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨s.min'_le k hk, s.le_max' k hk⟩
    have hnonneg : 0 ≤ q + 1 - p := by omega
    have hcast : (((q + 1 - p).toNat : ℕ) : ℝ) = (q : ℝ) + 1 - (p : ℝ) := by
      have he := Int.toNat_of_nonneg hnonneg
      exact_mod_cast he
    calc
      (s.card : ℝ) ≤ ((Finset.Icc p q).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (q : ℝ) + 1 - (p : ℝ) := by rw [Int.card_Icc, hcast]
      _ ≤ b - a + 1 := by linarith [(hs p hp).1, (hs q hq).2]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

/-- The exact factor used with a primitive lattice vector in the polar induction. -/
theorem card_le_three_halves_mul (s : Finset ℤ) {a b x ℓ : ℝ} (hab : a ≤ b)
    (hs : ∀ k ∈ s, a ≤ (k : ℝ) + x ∧ (k : ℝ) + x ≤ b)
    (hlen : b - a ≤ ℓ) (hℓ : 2 ≤ ℓ) : (s.card : ℝ) ≤ (3 / 2 : ℝ) * ℓ := by
  have h := card_le_length_add_one s hab hs
  linarith

/-- The original subtype cardinal, with finiteness produced from the interval bounds. -/
theorem natCard_integer_fiber_le_length_add_one {a b x : ℝ} (hab : a ≤ b) :
    (Nat.card {k : ℤ | a ≤ (k : ℝ) + x ∧ (k : ℝ) + x ≤ b} : ℝ) ≤ b - a + 1 := by
  classical
  have hf := finite_integer_fiber a b x
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hf]
  exact card_le_length_add_one hf.toFinset hab fun k hk => hf.mem_toFinset.mp hk

theorem natCard_integer_fiber_le_three_halves_mul {a b x ℓ : ℝ} (hab : a ≤ b)
    (hlen : b - a ≤ ℓ) (hℓ : 2 ≤ ℓ) :
    (Nat.card {k : ℤ | a ≤ (k : ℝ) + x ∧ (k : ℝ) + x ≤ b} : ℝ) ≤ (3 / 2 : ℝ) * ℓ := by
  have h := natCard_integer_fiber_le_length_add_one (x := x) hab
  linarith

end ArakelovGeometry.IntegerFiberCount

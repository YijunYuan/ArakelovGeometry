/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Rank blocks of complete finite flags

Successive rank intervals partition the ambient slots, including repeated
flag terms. Counting these intervals and summing over their fibres
generalizes the rank-block calculation for actual Hermitian HN factors.
-/

@[expose] public section

open scoped BigOperators

namespace Submodule

noncomputable section

variable {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Every ambient rank slot lies in a unique consecutive rank interval
of a full monotone flag; repeated terms create empty intervals. -/
theorem exists_unique_flag_rank_interval {n : ℕ} (U : Fin (n + 1) → Submodule K E)
    (hU : Monotone U) (hzero : U 0 = ⊥) (htop : U (Fin.last n) = ⊤)
    (j : Fin (Module.finrank K E)) :
    ∃! i : Fin n, Module.finrank K (U i.castSucc) ≤ j.val ∧
      j.val < Module.finrank K (U i.succ) := by
  classical
  have hex : ∃ k : Fin (n + 1), j.val < Module.finrank K (U k) := by
    refine ⟨Fin.last n, ?_⟩
    rw [htop, finrank_top]
    exact j.isLt
  let k := Fin.find (fun k : Fin (n + 1) ↦ j.val < Module.finrank K (U k)) hex
  have hk : j.val < Module.finrank K (U k) := Fin.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz, hzero, finrank_bot] at hk
    exact Nat.not_lt_zero j.val hk
  let i := k.pred hk0
  have hs : i.succ = k := Fin.succ_pred k hk0
  have hi1 : j.val < Module.finrank K (U i.succ) := by rwa [hs]
  have hi0 : Module.finrank K (U i.castSucc) ≤ j.val := by
    apply Nat.le_of_not_gt
    apply Fin.find_min hex
    change i.castSucc < k
    rw [← hs]
    exact i.castSucc_lt_succ
  refine ⟨i, ⟨hi0, hi1⟩, ?_⟩
  intro l hl
  apply Fin.ext
  by_cases hil : i.val < l.val
  · have hidx : i.succ ≤ l.castSucc := by change i.val + 1 ≤ l.val; omega
    have hd := Submodule.finrank_mono (hU hidx)
    omega
  · by_cases hli : l.val < i.val
    · have hidx : l.succ ≤ i.castSucc := by change l.val + 1 ≤ i.val; omega
      have hd := Submodule.finrank_mono (hU hidx)
      omega
    · omega

/-- Count a consecutive flag rank interval by its true dimension increment.
This is the finite rank-block bijection used for Hermitian HN factors. -/
theorem card_flag_rank_interval {n : ℕ} (U : Fin (n + 1) → Submodule K E) (i : Fin n) :
    (Finset.univ.filter (fun j : Fin (Module.finrank K E) ↦
      Module.finrank K (U i.castSucc) ≤ j.val ∧ j.val < Module.finrank K (U i.succ))).card =
        Module.finrank K (U i.succ) - Module.finrank K (U i.castSucc) := by
  classical
  let a := Module.finrank K (U i.castSucc)
  let b := Module.finrank K (U i.succ)
  have hb : b ≤ Module.finrank K E := Submodule.finrank_le _
  have hc : (Finset.univ.filter (fun j : Fin (Module.finrank K E) ↦
      a ≤ j.val ∧ j.val < b)).card = (Finset.Ico a b).card := by
    apply Finset.card_bij (fun j _ ↦ j.val)
    · intro j hj
      exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hj).2
    · intro j _ l _ hjl
      exact Fin.ext hjl
    · intro l hl
      have hl' := Finset.mem_Ico.mp hl
      let j : Fin (Module.finrank K E) := ⟨l, hl'.2.trans_le hb⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩, rfl⟩
  exact hc.trans (Nat.card_Ico a b)

/-- A real function constant on each genuine flag rank block sums with
its exact rank multiplicity, including the empty ambient list and repeated terms. -/
theorem sum_eq_sum_flag_rank_blocks {n : ℕ} (U : Fin (n + 1) → Submodule K E)
    (hU : Monotone U) (hzero : U 0 = ⊥) (htop : U (Fin.last n) = ⊤)
    (a : Fin (Module.finrank K E) → ℝ) (b : Fin n → ℝ)
    (hab : ∀ i j, Module.finrank K (U i.castSucc) ≤ j.val →
      j.val < Module.finrank K (U i.succ) → a j = b i) :
    (∑ j, a j) = ∑ i, ((Module.finrank K (U i.succ) -
      Module.finrank K (U i.castSucc) : ℕ) : ℝ) * b i := by
  classical
  let I := fun j : Fin (Module.finrank K E) ↦
    Classical.choose (exists_unique_flag_rank_interval U hU hzero htop j)
  have hI : ∀ j, Module.finrank K (U (I j).castSucc) ≤ j.val ∧
      j.val < Module.finrank K (U (I j).succ) := fun j ↦
    (Classical.choose_spec (exists_unique_flag_rank_interval U hU hzero htop j)).1
  have hiff : ∀ j i, I j = i ↔ Module.finrank K (U i.castSucc) ≤ j.val ∧
      j.val < Module.finrank K (U i.succ) := by
    intro j i
    constructor
    · rintro rfl
      exact hI j
    · intro hi
      exact ((Classical.choose_spec
        (exists_unique_flag_rank_interval U hU hzero htop j)).2 i hi).symm
  have hcard : ∀ i, (Finset.univ.filter (fun j ↦ I j = i)).card =
      Module.finrank K (U i.succ) - Module.finrank K (U i.castSucc) := by
    intro i
    simp only [hiff, card_flag_rank_interval]
  have he : ∀ j, b (I j) = a j := fun j ↦ (hab (I j) j (hI j).1 (hI j).2).symm
  have hs := Finset.sum_fiberwise' (Finset.univ : Finset (Fin (Module.finrank K E))) I b
  simpa only [Finset.sum_const, nsmul_eq_mul, hcard, he] using hs.symm

end

end Submodule

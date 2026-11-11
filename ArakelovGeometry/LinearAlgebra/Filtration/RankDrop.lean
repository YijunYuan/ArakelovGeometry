/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.Pairing

/-!
# Rank-sum drop for centered real filtrations

This is the algebraic rank-induction step on Bost page 32. A pair of centered
finite real filtrations with nonzero total intrinsic self-pairing has strictly
smaller rank sum on every pair of actual grades. The result includes zero grades
and zero-dimensional factors and does not assume tensor-HN compatibility.
-/

@[expose] public section

open Module
open scoped BigOperators

namespace Submodule

variable {K E F ι κ : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- An actual grade of a finite adapted filtration has rank at most the ambient rank. -/
theorem finrank_filtrationGraded_le_of_basis [Finite ι]
    (b : Basis ι K E) (a : ι → ℝ) {P : ℝ → Submodule K E}
    (hP : ∀ t, P t = span K (b '' {i | t ≤ a i})) (t : ℝ) :
    finrank K (FiltrationGraded P t) ≤ finrank K E := by
  classical
  let := Fintype.ofFinite ι
  rw [finrank_filtrationGraded_eq_card b a hP, finrank_eq_card_basis b]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

/-- A full-dimensional actual grade forces scalar adapted weights, hence self-pairing
equals its index times expectation. This identity also holds in ambient rank zero. -/
theorem filtrationPairing_self_eq_mul_expectation_of_full_grade [Finite ι]
    (b : Basis ι K E) (a : ι → ℝ) {P : ℝ → Submodule K E}
    (hP : ∀ t, P t = span K (b '' {i | t ≤ a i})) (t : ℝ)
    (hfull : finrank K (FiltrationGraded P t) = finrank K E) :
    filtrationPairing P P = t * filtrationExpectation P := by
  classical
  let := Fintype.ofFinite ι
  have hcard : (Finset.univ.filter fun i ↦ a i = t).card =
      (Finset.univ : Finset ι).card := by
    simpa only [finrank_filtrationGraded_eq_card b a hP, finrank_eq_card_basis b,
      Finset.card_univ] using hfull
  have ha (i : ι) : a i = t := Finset.card_filter_eq_iff.mp hcard i (Finset.mem_univ i)
  rw [filtrationPairing_eq_sum_weights b a a hP hP,
    filtrationExpectation_eq_sum_weights b a hP]
  calc
    (∑ i, a i * a i) / (finrank K E : ℝ) =
        (∑ i, t * a i) / (finrank K E : ℝ) := by
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ congrArg (· * a i) (ha i)
    _ = t * ((∑ i, a i) / (finrank K E : ℝ)) := by rw [← Finset.mul_sum, mul_div_assoc]

/-- Bost page 32's strict drop in the SUM of ranks, for every pair of actual grades.
Centering and nonzero total intrinsic self-pairing suffice, including zero-rank edges.
This makes the smaller-rank induction applicable; it does not prove that hypothesis. -/
theorem finrank_filtrationGraded_add_lt_of_centered [Finite ι] [Finite κ]
    (b : Basis ι K E) (c : Basis κ K F) (a : ι → ℝ) (d : κ → ℝ)
    {P : ℝ → Submodule K E} {R : ℝ → Submodule K F}
    (hP : ∀ t, P t = span K (b '' {i | t ≤ a i}))
    (hR : ∀ u, R u = span K (c '' {j | u ≤ d j}))
    (hPc : filtrationExpectation P = 0) (hRc : filtrationExpectation R = 0)
    (hne : filtrationPairing P P + filtrationPairing R R ≠ 0) (t u : ℝ) :
    finrank K (FiltrationGraded P t) + finrank K (FiltrationGraded R u) <
      finrank K E + finrank K F := by
  have hE := finrank_filtrationGraded_le_of_basis b a hP t
  have hF := finrank_filtrationGraded_le_of_basis c d hR u
  by_contra hn
  have he : finrank K (FiltrationGraded P t) = finrank K E := by omega
  have hf : finrank K (FiltrationGraded R u) = finrank K F := by omega
  apply hne
  rw [filtrationPairing_self_eq_mul_expectation_of_full_grade b a hP t he,
    filtrationPairing_self_eq_mul_expectation_of_full_grade c d hR u hf, hPc, hRc]
  simp

end Submodule

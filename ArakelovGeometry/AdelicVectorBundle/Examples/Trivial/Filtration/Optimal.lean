/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.QuotientDegree
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Variation
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Lattice

/-!
# Conditional minimization for actual tensor quotient filtrations

The coordinate energy retains the reciprocal dimension of each factor.
Every coordinate expression below is connected to the intrinsic filtration
pairing or to the proved actual quotient finite maximum.
-/

@[expose] public section

open Module
open scoped BigOperators TensorProduct

namespace Submodule

variable {J : Type*} [Fintype J]

/-- The sum of the mean squared weights, with a separate rank for each factor. -/
noncomputable def filtrationWeightEnergy (a : J → ℕ) (w : ∀ j, Fin (a j) → ℝ) : ℝ :=
  ∑ j, (∑ i, w j i ^ 2) / a j

/-- Centered weights with total intrinsic self-pairing one. -/
def centeredWeightSphere (a : J → ℕ) : Set (∀ j, Fin (a j) → ℝ) :=
  {w | (∀ j, ∑ i, w j i = 0) ∧ filtrationWeightEnergy a w = 1}

theorem filtrationWeightEnergy_nonneg (a : J → ℕ) (w : ∀ j, Fin (a j) → ℝ) :
    0 ≤ filtrationWeightEnergy a w :=
  Finset.sum_nonneg fun j _ ↦ div_nonneg
    (Finset.sum_nonneg fun i _ ↦ sq_nonneg (w j i)) (Nat.cast_nonneg _)

theorem continuous_filtrationWeightEnergy (a : J → ℕ) :
    Continuous (filtrationWeightEnergy a) := by
  unfold filtrationWeightEnergy
  fun_prop

theorem isClosed_centeredWeightSphere (a : J → ℕ) :
    IsClosed (centeredWeightSphere a) := by
  apply IsClosed.inter
  · exact isClosed_iInter fun j ↦ isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (continuous_filtrationWeightEnergy a) continuous_const

/-- The weighted centered unit sphere is compact in the fixed finite coordinate space. -/
theorem isCompact_centeredWeightSphere (a : J → ℕ) (ha : ∀ j, 0 < a j) :
    IsCompact (centeredWeightSphere a) := by
  classical
  let box : Set (∀ j, Fin (a j) → ℝ) :=
    Set.univ.pi fun j ↦ Set.univ.pi fun _ ↦ Set.Icc (-(a j : ℝ) - 1) (a j + 1)
  have hbox : IsCompact box :=
    isCompact_pi_infinite fun _ ↦ isCompact_pi_infinite fun _ ↦ isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_centeredWeightSphere a)
  intro w hw
  simp only [box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro j i
  have hj : (∑ k, w j k ^ 2) / (a j : ℝ) ≤ filtrationWeightEnergy a w :=
    Finset.single_le_sum (fun k _ ↦ div_nonneg
      (Finset.sum_nonneg fun l _ ↦ sq_nonneg (w k l)) (Nat.cast_nonneg _))
      (Finset.mem_univ j)
  rw [hw.2] at hj
  have hd : (0 : ℝ) < a j := Nat.cast_pos.mpr (ha j)
  have hi : w j i ^ 2 ≤ ∑ k, w j k ^ 2 :=
    Finset.single_le_sum (fun k _ ↦ sq_nonneg (w j k)) (Finset.mem_univ i)
  have hsq : w j i ^ 2 ≤ (a j : ℝ) :=
    hi.trans (by simpa using (div_le_iff₀ hd).mp hj)
  have habs : |w j i| ≤ (a j : ℝ) + 1 :=
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (a j : ℝ)]) (by positivity)
  simpa only [neg_add_rev, add_comm] using abs_le.mp habs

variable {K : Type*} [Field K] {E : J → Type*}
  [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)]
  [∀ j, FiniteDimensional K (E j)]

/-- The coordinate energy is the actual intrinsic sum of self-pairings. -/
theorem filtrationWeightEnergy_eq_pairing
    (b : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
    (w : ∀ j, Fin (finrank K (E j)) → ℝ) :
    filtrationWeightEnergy (fun j ↦ finrank K (E j)) w =
      ∑ j, filtrationPairing (fun t ↦ span K (b j '' {i | t ≤ w j i}))
        (fun t ↦ span K (b j '' {i | t ≤ w j i})) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [filtrationPairing_eq_sum_weights (b j) (w j) (w j) (fun _ ↦ rfl) (fun _ ↦ rfl)]
  simp only [pow_two]

end Submodule

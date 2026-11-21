/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.Equiv

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.QuotientDegree
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Variation
public import Mathlib.Algebra.Order.GroupWithZero.Finset
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Lattice

/-!
# Conditional minimization for tensor quotient filtrations

A centered negative candidate yields a normalized global minimum over all
admissible finite real filtrations. The coordinate energy retains the reciprocal
dimension of each factor and agrees with the intrinsic filtration pairing.

This file proves finite-family existence and uniqueness and a binary quotient
specialization of the optimization results in [ChenMoriwaki2020], Section 5.4.
The candidate is assumed, and the general variational inequality (5.13) is not
proved here.
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

theorem filtrationWeightEnergy_mul (a : J → ℕ) (w : ∀ j, Fin (a j) → ℝ) (t : ℝ) :
    filtrationWeightEnergy a (fun j i ↦ t * w j i) = t ^ 2 * filtrationWeightEnergy a w := by
  simp only [filtrationWeightEnergy, mul_pow, ← Finset.mul_sum, mul_div_assoc]

/-- The strict midpoint identity uses the original reciprocal-rank weights. -/
theorem filtrationWeightEnergy_midpoint (a : J → ℕ) (x y : ∀ j, Fin (a j) → ℝ) :
    filtrationWeightEnergy a (fun j i ↦ (x j i + y j i) / 2) =
      (filtrationWeightEnergy a x + filtrationWeightEnergy a y) / 2 -
        filtrationWeightEnergy a (fun j i ↦ x j i - y j i) / 4 := by
  have hpoint (j : J) (i : Fin (a j)) :
      ((x j i + y j i) / 2) ^ 2 =
        x j i ^ 2 / 2 + y j i ^ 2 / 2 - (x j i - y j i) ^ 2 / 4 := by ring
  simp only [filtrationWeightEnergy]
  simp_rw [hpoint]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_div, sub_div, add_div, div_right_comm]

theorem filtrationWeightEnergy_eq_zero_iff (a : J → ℕ) (ha : ∀ j, 0 < a j)
    (w : ∀ j, Fin (a j) → ℝ) :
    filtrationWeightEnergy a w = 0 ↔ ∀ j i, w j i = 0 := by
  classical
  unfold filtrationWeightEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ div_nonneg
    (Finset.sum_nonneg fun i _ ↦ sq_nonneg (w j i)) (Nat.cast_nonneg (a j)))]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h j
    have hj := h j
    rw [div_eq_zero_iff] at hj
    have hs : ∑ i, w j i ^ 2 = 0 := hj.resolve_right (ne_of_gt (Nat.cast_pos.mpr (ha j)))
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (w j i))).mp hs
    intro i
    exact sq_eq_zero_iff.mp (hh i (Finset.mem_univ i))
  · intro h j
    simp [h]

/-- Every nonzero centered weight family has an actual unit normalization. -/
theorem normalize_mem_centeredWeightSphere (a : J → ℕ)
    (w : ∀ j, Fin (a j) → ℝ) (hc : ∀ j, ∑ i, w j i = 0)
    (hp : 0 < filtrationWeightEnergy a w) :
    (fun j i ↦ (Real.sqrt (filtrationWeightEnergy a w))⁻¹ * w j i) ∈
      centeredWeightSphere a := by
  refine ⟨fun j ↦ ?_, ?_⟩
  · rw [← Finset.mul_sum, hc j, mul_zero]
  · rw [filtrationWeightEnergy_mul, inv_pow,
      Real.sq_sqrt (filtrationWeightEnergy_nonneg a w), inv_mul_cancel₀ hp.ne']

theorem continuous_filtrationWeightEnergy (a : J → ℕ) :
    Continuous (filtrationWeightEnergy a) := by
  unfold filtrationWeightEnergy
  fun_prop

theorem isClosed_centeredWeightSphere (a : J → ℕ) :
    IsClosed (centeredWeightSphere a) := by
  apply IsClosed.inter
  · have h : ∀ j, IsClosed {w : ∀ j, Fin (a j) → ℝ | ∑ i, w j i = 0} :=
      fun _ ↦ isClosed_eq (by fun_prop) continuous_const
    have he : {w : ∀ j, Fin (a j) → ℝ | ∀ j, ∑ i, w j i = 0} =
        ⋂ j, {w : ∀ j, Fin (a j) → ℝ | ∑ i, w j i = 0} := by
      ext w
      simp
    change IsClosed {w : ∀ j, Fin (a j) → ℝ | ∀ j, ∑ i, w j i = 0}
    rw [he]
    exact isClosed_iInter h
  · exact isClosed_eq (continuous_filtrationWeightEnergy a) continuous_const

/-- The weighted centered unit sphere is compact in the fixed finite coordinate space. -/
theorem isCompact_centeredWeightSphere (a : J → ℕ) (ha : ∀ j, 0 < a j) :
    IsCompact (centeredWeightSphere a) := by
  classical
  let box : Set (∀ j, Fin (a j) → ℝ) :=
    {w | ∀ j i, w j i ∈ Set.Icc (-(a j : ℝ) - 1) (a j + 1)}
  have hbox : IsCompact box :=
    isCompact_pi_infinite fun _ ↦ isCompact_pi_infinite fun _ ↦ isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_centeredWeightSphere a)
  intro w hw
  simp only [box, Set.mem_ofPred_eq, Set.mem_Icc]
  intro j i
  have hj : (∑ k, w j k ^ 2) / (a j : ℝ) ≤ filtrationWeightEnergy a w := by
    unfold filtrationWeightEnergy
    apply Finset.single_le_sum (f := fun k : J ↦ (∑ l : Fin (a k), w k l ^ 2) / (a k : ℝ))
    · intro k _
      exact div_nonneg (Finset.sum_nonneg fun l _ ↦ sq_nonneg (w k l)) (Nat.cast_nonneg (a k))
    · exact Finset.mem_univ j
  rw [hw.2] at hj
  have hd : (0 : ℝ) < a j := Nat.cast_pos.mpr (ha j)
  have hi : w j i ^ 2 ≤ ∑ k, w j k ^ 2 :=
    Finset.single_le_sum (fun k _ ↦ sq_nonneg (w j k)) (Finset.mem_univ i)
  have hsq : w j i ^ 2 ≤ (a j : ℝ) :=
    hi.trans (by simpa using (div_le_iff₀ hd).mp hj)
  have habs : |w j i| ≤ (a j : ℝ) + 1 :=
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (a j : ℝ)]) (by positivity)
  obtain ⟨hl, hr⟩ := abs_le.mp habs
  exact ⟨by linarith, hr⟩

variable {K : Type*} [Field K] {E : J → Type*}
  [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)]

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

variable {Q : Type*} [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- In a fixed family of actual bases, the quotient expectation is continuous
in the weights, by the proved determinant maximum formula. -/
theorem continuous_filtrationExpectation_piTensor_image
    (b : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
    (q : (⨂[K] j, E j) →ₗ[K] Q) (hq : Function.Surjective q) :
    Continuous (fun w : ∀ j, Fin (finrank K (E j)) → ℝ ↦
      filtrationExpectation (fun t ↦
        (piTensorFiltration (fun j s ↦ span K (b j '' {i | s ≤ w j i})) t).map q)) := by
  have he (w : ∀ j, Fin (finrank K (E j)) → ℝ) :=
    filtrationExpectation_piTensor_image_eq_sup' b w (fun _ _ ↦ rfl)
      (Module.finBasis K Q) q hq
  simp_rw [he]
  apply Continuous.div_const
  apply Continuous.finset_sup'_apply
  intro σ _
  fun_prop

/-- Nonnegative dilation of actual factor weights scales the actual quotient expectation. -/
theorem filtrationExpectation_piTensor_image_mul
    (b : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
    (q : (⨂[K] j, E j) →ₗ[K] Q) (hq : Function.Surjective q)
    (w : ∀ j, Fin (finrank K (E j)) → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    filtrationExpectation (fun u ↦
      (piTensorFiltration (fun j s ↦ span K (b j '' {i | s ≤ t * w j i})) u).map q) =
      t * filtrationExpectation (fun u ↦
        (piTensorFiltration (fun j s ↦ span K (b j '' {i | s ≤ w j i})) u).map q) := by
  rw [filtrationExpectation_piTensor_image_eq_sup' b _ (fun _ _ ↦ rfl)
      (Module.finBasis K Q) q hq,
    filtrationExpectation_piTensor_image_eq_sup' b w (fun _ _ ↦ rfl)
      (Module.finBasis K Q) q hq]
  simp only [← Finset.mul_sum]
  rw [← Finset.mul₀_sup' ht, mul_div_assoc]

/-- An actual negative quotient candidate has positive intrinsic coordinate energy. -/
theorem filtrationWeightEnergy_pos_of_negative
    (b : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
    (q : (⨂[K] j, E j) →ₗ[K] Q) (hq : Function.Surjective q)
    (ha : ∀ j, 0 < finrank K (E j)) (w : ∀ j, Fin (finrank K (E j)) → ℝ)
    (hneg : filtrationExpectation (fun t ↦
      (piTensorFiltration (fun j s ↦ span K (b j '' {i | s ≤ w j i})) t).map q) < 0) :
    0 < filtrationWeightEnergy (fun j ↦ finrank K (E j)) w := by
  apply lt_of_le_of_ne (filtrationWeightEnergy_nonneg _ w)
  intro hz
  have hw := (filtrationWeightEnergy_eq_zero_iff _ ha w).mp hz.symm
  rw [filtrationExpectation_piTensor_image_eq_sup' b w (fun _ _ ↦ rfl)
    (Module.finBasis K Q) q hq] at hneg
  simp [hw] at hneg

/-- The actual quotient expectation is convex at a common-basis midpoint. -/
theorem filtrationExpectation_piTensor_image_midpoint_le
    (b : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
    (q : (⨂[K] j, E j) →ₗ[K] Q) (hq : Function.Surjective q)
    (x y : ∀ j, Fin (finrank K (E j)) → ℝ) :
    filtrationExpectation (fun t ↦ (piTensorFiltration
      (fun j s ↦ span K (b j '' {i | s ≤ (x j i + y j i) / 2})) t).map q) ≤
      (filtrationExpectation (fun t ↦ (piTensorFiltration
        (fun j s ↦ span K (b j '' {i | s ≤ x j i})) t).map q) +
       filtrationExpectation (fun t ↦ (piTensorFiltration
        (fun j s ↦ span K (b j '' {i | s ≤ y j i})) t).map q)) / 2 := by
  let S := quotientDeterminantSupport (Basis.piTensorProduct b) (Module.finBasis K Q) q
  have hs : S.Nonempty := quotientDeterminantSupport_nonempty _ _ _ hq
  let L (w : ∀ j, Fin (finrank K (E j)) → ℝ) (σ : Fin (finrank K Q) →
      (∀ j, Fin (finrank K (E j)))) := ∑ k, ∑ j, w j (σ k j)
  have hm : S.sup' hs (L (fun j i ↦ (x j i + y j i) / 2)) ≤
      (S.sup' hs (L x) + S.sup' hs (L y)) / 2 := by
    apply Finset.sup'_le
    intro σ hσ
    have hx := Finset.le_sup' (L x) hσ
    have hy := Finset.le_sup' (L y) hσ
    have he : L (fun j i ↦ (x j i + y j i) / 2) σ = (L x σ + L y σ) / 2 := by
      simp only [L, ← Finset.sum_div, Finset.sum_add_distrib]
    rw [he]
    linarith
  rw [filtrationExpectation_piTensor_image_eq_sup' b _ (fun _ _ ↦ rfl)
      (Module.finBasis K Q) q hq,
    filtrationExpectation_piTensor_image_eq_sup' b x (fun _ _ ↦ rfl)
      (Module.finBasis K Q) q hq,
    filtrationExpectation_piTensor_image_eq_sup' b y (fun _ _ ↦ rfl)
      (Module.finBasis K Q) q hq]
  calc
    _ ≤ ((S.sup' hs (L x) + S.sup' hs (L y)) / 2) / (finrank K Q : ℝ) :=
      div_le_div_of_nonneg_right hm (Nat.cast_nonneg _)
    _ = _ := by ring

/-- For every actual family of bases, the quotient expectation attains its
minimum on the centered weighted unit sphere. -/
theorem exists_minimum_in_basis
    (b : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
    (q : (⨂[K] j, E j) →ₗ[K] Q) (hq : Function.Surjective q)
    (ha : ∀ j, 0 < finrank K (E j))
    (hS : (centeredWeightSphere (fun j ↦ finrank K (E j))).Nonempty) :
    ∃ w ∈ centeredWeightSphere (fun j ↦ finrank K (E j)),
      ∀ z ∈ centeredWeightSphere (fun j ↦ finrank K (E j)),
        filtrationExpectation (fun t ↦
          (piTensorFiltration (fun j s ↦ span K (b j '' {i | s ≤ w j i})) t).map q) ≤
        filtrationExpectation (fun t ↦
          (piTensorFiltration (fun j s ↦ span K (b j '' {i | s ≤ z j i})) t).map q) :=
  (isCompact_centeredWeightSphere _ ha).exists_isMinOn hS
    (continuous_filtrationExpectation_piTensor_image b q hq).continuousOn

/-- Actual basis families with the same determinant support have the same
quotient expectation as a function of weights. -/
theorem quotient_expectation_eq_of_support_eq
    (b b' : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
    (q : (⨂[K] j, E j) →ₗ[K] Q) (hq : Function.Surjective q)
    (hs : quotientDeterminantSupport (Basis.piTensorProduct b) (Module.finBasis K Q) q =
      quotientDeterminantSupport (Basis.piTensorProduct b') (Module.finBasis K Q) q)
    (w : ∀ j, Fin (finrank K (E j)) → ℝ) :
    filtrationExpectation (fun t ↦
      (piTensorFiltration (fun j s ↦ span K (b j '' {i | s ≤ w j i})) t).map q) =
    filtrationExpectation (fun t ↦
      (piTensorFiltration (fun j s ↦ span K (b' j '' {i | s ≤ w j i})) t).map q) := by
  rw [filtrationExpectation_piTensor_image_eq_sup' b w (fun _ _ ↦ rfl)
      (Module.finBasis K Q) q hq,
    filtrationExpectation_piTensor_image_eq_sup' b' w (fun _ _ ↦ rfl)
      (Module.finBasis K Q) q hq]
  congr 1
  congr 1

/-- Minimize over the finite set of actually realized supports. The returned
support comes with an actual family of bases, hence actual filtrations. -/
theorem exists_global_unit_minimum_weights
    (b₀ : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
    (q : (⨂[K] j, E j) →ₗ[K] Q) (hq : Function.Surjective q)
    (ha : ∀ j, 0 < finrank K (E j))
    (hS : (centeredWeightSphere (fun j ↦ finrank K (E j))).Nonempty) :
    ∃ (b : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
      (w : ∀ j, Fin (finrank K (E j)) → ℝ),
      w ∈ centeredWeightSphere (fun j ↦ finrank K (E j)) ∧
      ∀ (b' : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
        (z : ∀ j, Fin (finrank K (E j)) → ℝ),
        z ∈ centeredWeightSphere (fun j ↦ finrank K (E j)) →
        filtrationExpectation (fun t ↦
          (piTensorFiltration (fun j s ↦ span K (b j '' {i | s ≤ w j i})) t).map q) ≤
        filtrationExpectation (fun t ↦
          (piTensorFiltration (fun j s ↦ span K (b' j '' {i | s ≤ z j i})) t).map q) := by
  classical
  let B := ∀ j, Basis (Fin (finrank K (E j))) K (E j)
  let support (b : B) :=
    quotientDeterminantSupport (Basis.piTensorProduct b) (Module.finBasis K Q) q
  let R := Set.range support
  have hr (s : R) : ∃ b : B, support b = s.val := s.property
  choose basis hb using hr
  have hm (s : R) := exists_minimum_in_basis (basis s) q hq ha hS
  choose weight hw hmin using hm
  let value (s : R) := filtrationExpectation (fun t ↦
    (piTensorFiltration (fun j u ↦ span K (basis s j '' {i | u ≤ weight s j i})) t).map q)
  let := Fintype.ofFinite R
  have hn : (Finset.univ : Finset R).Nonempty :=
    ⟨⟨support b₀, ⟨b₀, rfl⟩⟩, Finset.mem_univ _⟩
  obtain ⟨s, _, hs⟩ := Finset.exists_min_image Finset.univ value hn
  refine ⟨basis s, weight s, hw s, ?_⟩
  intro b' z hz
  let t : R := ⟨support b', ⟨b', rfl⟩⟩
  calc
    value s ≤ value t := hs t (Finset.mem_univ t)
    _ ≤ filtrationExpectation (fun u ↦
        (piTensorFiltration (fun j v ↦ span K (basis t j '' {i | v ≤ z j i})) u).map q) :=
      hmin t z hz
    _ = _ := quotient_expectation_eq_of_support_eq (basis t) b' q hq (hb t) z

section NegativeMinimum

set_option quotPrecheck false in
local notation "Weights" => (∀ j, Fin (finrank K (E j)) → ℝ)
set_option quotPrecheck false in
local notation "Bases" => (∀ j, Basis (Fin (finrank K (E j))) K (E j))
local notation "energy" => filtrationWeightEnergy (fun j ↦ finrank K (E j))
local notation "sphere" => centeredWeightSphere (fun j ↦ finrank K (E j))

variable (q : (⨂[K] j, E j) →ₗ[K] Q) (hq : Function.Surjective q)

include hq

set_option quotPrecheck false in
local notation "M" => (fun (b : Bases) (w : Weights) ↦ filtrationExpectation (fun t ↦
  (piTensorFiltration (fun j s ↦ span K (b j '' {i | s ≤ w j i})) t).map q))

/-- Unit normalization preserves the normalized actual quotient payoff. -/
theorem quotient_expectation_normalize (b : Bases) (w : Weights) :
    M b (fun j i ↦ (Real.sqrt (energy w))⁻¹ * w j i) =
      M b w / Real.sqrt (energy w) := by
  simpa only [div_eq_mul_inv, mul_comm] using
    filtrationExpectation_piTensor_image_mul b q hq w (Real.sqrt (energy w))⁻¹
      (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- A negative actual quotient candidate yields a negative global minimum
among all centered weighted basis realizations, with positive denominator. -/
theorem exists_negative_global_minimum_weights
    (ha : ∀ j, 0 < finrank K (E j)) (b₀ : Bases) (w₀ : Weights)
    (hc₀ : ∀ j, ∑ i, w₀ j i = 0) (hneg₀ : M b₀ w₀ < 0) :
    ∃ (b : Bases) (w : Weights), w ∈ sphere ∧ M b w < 0 ∧
      ∀ (b' : Bases) (z : Weights), (∀ j, ∑ i, z j i = 0) → 0 < energy z →
        M b w ≤ M b' z / Real.sqrt (energy z) := by
  have hp := filtrationWeightEnergy_pos_of_negative b₀ q hq ha w₀ hneg₀
  have hnorm₀ := normalize_mem_centeredWeightSphere _ w₀ hc₀ hp
  obtain ⟨b, w, hw, hmin⟩ := exists_global_unit_minimum_weights b₀ q hq ha ⟨_, hnorm₀⟩
  refine ⟨b, w, hw, ?_, ?_⟩
  · have h := hmin b₀ _ hnorm₀
    have hle := h.trans_eq (quotient_expectation_normalize q hq b₀ w₀)
    exact hle.trans_lt (div_neg_of_neg_of_pos hneg₀ (Real.sqrt_pos.mpr hp))
  · intro b' z hc hz
    have h := hmin b' _ (normalize_mem_centeredWeightSphere _ z hc hz)
    exact h.trans_eq (quotient_expectation_normalize q hq b' z)

end NegativeMinimum

section ActualFiltrations

variable [∀ j, FiniteDimensional K (E j)]

set_option quotPrecheck false in
local notation "Families" => (∀ j, ℝ → Submodule K (E j))
set_option quotPrecheck false in
local notation "Admissible" => (fun F : Families ↦ ∀ j,
  Antitone (F j) ∧ (∃ t, F j t = ⊥) ∧ (∃ t, F j t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F j s = F j t) ∧
  filtrationExpectation (F j) = 0)
set_option quotPrecheck false in
local notation "Energy" => (fun F : Families ↦ ∑ j, filtrationPairing (F j) (F j))

omit [Fintype J] in
private theorem exists_centered_coordinates
    (ha : ∀ j, 0 < finrank K (E j)) (F : Families) (hF : Admissible F) :
    ∃ (b : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
      (w : ∀ j, Fin (finrank K (E j)) → ℝ),
      (∀ j, ∑ i, w j i = 0) ∧
      F = fun j t ↦ span K (b j '' {i | t ≤ w j i}) := by
  classical
  have hex j := exists_common_weighted_basis (hF j).1 (hF j).2.1 (hF j).2.2.1
    (hF j).2.2.2.1 (hF j).1 (hF j).2.1 (hF j).2.2.1 (hF j).2.2.2.1
  choose b w z hw hz hcoord hcoord' using hex
  refine ⟨b, w, ?_, funext fun j ↦ funext (hw j)⟩
  intro j
  have he := (hF j).2.2.2.2
  rw [filtrationExpectation_eq_sum_weights (b j) (w j) (hw j)] at he
  exact (div_eq_zero_iff.mp he).resolve_right (ne_of_gt (Nat.cast_pos.mpr (ha j)))

omit [Fintype J] in
private theorem admissible_weightedSpans
    (b : ∀ j, Basis (Fin (finrank K (E j))) K (E j))
    (w : ∀ j, Fin (finrank K (E j)) → ℝ) (hc : ∀ j, ∑ i, w j i = 0) :
    Admissible (fun j t ↦ span K (b j '' {i | t ≤ w j i})) := by
  intro j
  obtain ⟨hb, ht⟩ := span_weights_attains_bot_top (b j) (w j)
  refine ⟨antitone_span_weights (b j) (w j), hb, ht,
    span_weights_locallyConstant_left (b j) (w j), ?_⟩
  rw [filtrationExpectation_eq_sum_weights (b j) (w j) (fun _ ↦ rfl), hc j, zero_div]

variable (q : (⨂[K] j, E j) →ₗ[K] Q) (hq : Function.Surjective q)

set_option quotPrecheck false in
local notation "Value" => (fun F : Families ↦
  filtrationExpectation (fun t ↦ (piTensorFiltration F t).map q))

include hq

/-- Existence of an actual centered unit global optimizer, conditional only
on one actual centered negative quotient-filtration candidate. -/
theorem exists_normalized_quotient_optimizer
    (ha : ∀ j, 0 < finrank K (E j)) (F₀ : Families)
    (hF₀ : Admissible F₀) (hneg₀ : Value F₀ < 0) :
    ∃ P : Families, Admissible P ∧ Energy P = 1 ∧ Value P < 0 ∧
      ∀ F : Families, Admissible F → 0 < Energy F →
        Value P ≤ Value F / Real.sqrt (Energy F) := by
  obtain ⟨b₀, w₀, hc₀, he₀⟩ := exists_centered_coordinates ha F₀ hF₀
  rw [he₀] at hneg₀
  obtain ⟨b, w, hw, hneg, hmin⟩ :=
    exists_negative_global_minimum_weights q hq ha b₀ w₀ hc₀ hneg₀
  let P : Families := fun j t ↦ span K (b j '' {i | t ≤ w j i})
  have hP : Admissible P := by
    intro j
    obtain ⟨hb, ht⟩ := span_weights_attains_bot_top (b j) (w j)
    refine ⟨antitone_span_weights (b j) (w j), hb, ht,
      span_weights_locallyConstant_left (b j) (w j), ?_⟩
    rw [filtrationExpectation_eq_sum_weights (b j) (w j) (fun _ ↦ rfl), hw.1 j, zero_div]
  have hE : Energy P = 1 := (filtrationWeightEnergy_eq_pairing b w).symm.trans hw.2
  refine ⟨P, hP, hE, hneg, ?_⟩
  intro F hF hpos
  obtain ⟨b', z, hc, he⟩ := exists_centered_coordinates ha F hF
  rw [he] at hpos ⊢
  have henergy := filtrationWeightEnergy_eq_pairing b' z
  dsimp only at hpos ⊢
  rw [← henergy] at hpos ⊢
  exact hmin b' z hc hpos

/-- Two centered unit global minimizers of negative value are equal as actual
filtration functions. The proof compares their weights in common adapted bases. -/
theorem normalized_quotient_optimizer_unique
    (ha : ∀ j, 0 < finrank K (E j)) (P R : Families)
    (hP : Admissible P) (hR : Admissible R)
    (hPE : Energy P = 1) (hRE : Energy R = 1) (hneg : Value P < 0)
    (hPmin : ∀ F : Families, Admissible F → 0 < Energy F →
      Value P ≤ Value F / Real.sqrt (Energy F))
    (hRmin : ∀ F : Families, Admissible F → 0 < Energy F →
      Value R ≤ Value F / Real.sqrt (Energy F)) : P = R := by
  classical
  have hval : Value P = Value R := by
    have hpr := hPmin R hR (by rw [hRE]; norm_num)
    have hrp := hRmin P hP (by rw [hPE]; norm_num)
    rw [hRE, Real.sqrt_one, div_one] at hpr
    rw [hPE, Real.sqrt_one, div_one] at hrp
    exact le_antisymm hpr hrp
  have hex j := exists_common_weighted_basis (hP j).1 (hP j).2.1 (hP j).2.2.1
    (hP j).2.2.2.1 (hR j).1 (hR j).2.1 (hR j).2.2.1 (hR j).2.2.2.1
  choose b x y hx hy hxc hyc using hex
  have heP : P = fun j t ↦ span K (b j '' {i | t ≤ x j i}) :=
    funext fun j ↦ funext (hx j)
  have heR : R = fun j t ↦ span K (b j '' {i | t ≤ y j i}) :=
    funext fun j ↦ funext (hy j)
  have hcx (j : J) : ∑ i, x j i = 0 := by
    have hh := (hP j).2.2.2.2
    rw [filtrationExpectation_eq_sum_weights (b j) (x j) (hx j)] at hh
    exact (div_eq_zero_iff.mp hh).resolve_right (ne_of_gt (Nat.cast_pos.mpr (ha j)))
  have hcy (j : J) : ∑ i, y j i = 0 := by
    have hh := (hR j).2.2.2.2
    rw [filtrationExpectation_eq_sum_weights (b j) (y j) (hy j)] at hh
    exact (div_eq_zero_iff.mp hh).resolve_right (ne_of_gt (Nat.cast_pos.mpr (ha j)))
  let z := fun j i ↦ (x j i + y j i) / 2
  let Z : Families := fun j t ↦ span K (b j '' {i | t ≤ z j i})
  have hcz (j : J) : ∑ i, z j i = 0 := by
    simp only [z, ← Finset.sum_div, Finset.sum_add_distrib, hcx, hcy, zero_add, zero_div]
  have hZ : Admissible Z := admissible_weightedSpans b z hcz
  have hmid : Value Z ≤ Value P := by
    have hh := filtrationExpectation_piTensor_image_midpoint_le b q hq x y
    have hh' : Value Z ≤ (Value P + Value R) / 2 := by
      simpa only [heP, heR] using hh
    rw [← hval] at hh'
    linarith
  let a := fun j ↦ finrank K (E j)
  have hpos : 0 < filtrationWeightEnergy a z :=
    filtrationWeightEnergy_pos_of_negative b q hq ha z (hmid.trans_lt hneg)
  have heZ : filtrationWeightEnergy a z = Energy Z := filtrationWeightEnergy_eq_pairing b z
  have heX : filtrationWeightEnergy a x = 1 := by
    rw [filtrationWeightEnergy_eq_pairing b x]
    simpa only [heP] using hPE
  have heY : filtrationWeightEnergy a y = 1 := by
    rw [filtrationWeightEnergy_eq_pairing b y]
    simpa only [heR] using hRE
  have hmin := hPmin Z hZ (heZ ▸ hpos)
  have hspos : 0 < Real.sqrt (Energy Z) := Real.sqrt_pos.mpr (heZ ▸ hpos)
  have hmul := (le_div_iff₀ hspos).mp hmin
  have hnorm : 1 ≤ Real.sqrt (Energy Z) := by nlinarith
  have hsquare := Real.sq_sqrt (le_of_lt (heZ ▸ hpos))
  have hge : 1 ≤ Energy Z := by nlinarith
  have hid := filtrationWeightEnergy_midpoint a x y
  change filtrationWeightEnergy a z = _ at hid
  rw [heX, heY, heZ] at hid
  have hd : filtrationWeightEnergy a (fun j i ↦ x j i - y j i) = 0 := by
    have hn := filtrationWeightEnergy_nonneg a (fun j i ↦ x j i - y j i)
    linarith
  have hxy := (filtrationWeightEnergy_eq_zero_iff a ha _).mp hd
  have he : x = y := funext fun j ↦ funext fun i ↦ sub_eq_zero.mp (hxy j i)
  rw [heP, heR, he]

/-- The independent conditional optimizer: one actual centered negative
candidate gives a unique unit-normalized global minimizer among all actual
centered real filtrations. No geometric instability or optimality premise is used. -/
theorem exists_unique_normalized_quotient_optimizer
    (ha : ∀ j, 0 < finrank K (E j)) (F₀ : Families)
    (hF₀ : Admissible F₀) (hneg₀ : Value F₀ < 0) :
    ∃! P : Families, Admissible P ∧ Energy P = 1 ∧ Value P < 0 ∧
      ∀ F : Families, Admissible F → 0 < Energy F →
        Value P ≤ Value F / Real.sqrt (Energy F) := by
  obtain ⟨P, hP, hPE, hneg, hmin⟩ := exists_normalized_quotient_optimizer q hq ha F₀ hF₀ hneg₀
  refine ⟨P, ⟨hP, hPE, hneg, hmin⟩, ?_⟩
  rintro R ⟨hR, hRE, _, hRmin⟩
  exact (normalized_quotient_optimizer_unique q hq ha P R hP hR hPE hRE hneg hmin hRmin).symm

end ActualFiltrations

end Submodule

namespace Submodule

open ArakelovGeometry
open scoped TensorProduct

section Binary

universe u

variable {K : Type*} [Field K] {E V : Type u} {Q : Type*}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

set_option quotPrecheck false in
local notation "CenteredE" => (fun F : ℝ → Submodule K E ↦
  Antitone F ∧ (∃ t, F t = ⊥) ∧ (∃ t, F t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) ∧ filtrationExpectation F = 0)
set_option quotPrecheck false in
local notation "CenteredV" => (fun G : ℝ → Submodule K V ↦
  Antitone G ∧ (∃ t, G t = ⊥) ∧ (∃ t, G t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → G s = G t) ∧ filtrationExpectation G = 0)

/-- The direct ordinary binary tensor interface: an actual centered negative
candidate gives an actual centered unit global minimum. -/
private theorem exists_normalized_tensor_quotient_optimizer_sameUniverse
    (q : E ⊗[K] V →ₗ[K] Q) (hq : Function.Surjective q)
    (hE : 0 < finrank K E) (hV : 0 < finrank K V)
    (F₀ : ℝ → Submodule K E) (G₀ : ℝ → Submodule K V)
    (hF₀ : CenteredE F₀) (hG₀ : CenteredV G₀)
    (hneg₀ : filtrationExpectation (fun t ↦ (tensorFiltration F₀ G₀ t).map q) < 0) :
    ∃ (P : ℝ → Submodule K E) (R : ℝ → Submodule K V),
      CenteredE P ∧ CenteredV R ∧ filtrationPairing P P + filtrationPairing R R = 1 ∧
      filtrationExpectation (fun t ↦ (tensorFiltration P R t).map q) < 0 ∧
      ∀ (F : ℝ → Submodule K E) (G : ℝ → Submodule K V),
        CenteredE F → CenteredV G → 0 < filtrationPairing F F + filtrationPairing G G →
        filtrationExpectation (fun t ↦ (tensorFiltration P R t).map q) ≤
          filtrationExpectation (fun t ↦ (tensorFiltration F G t).map q) /
            Real.sqrt (filtrationPairing F F + filtrationPairing G G) := by
  let e := binaryTensorEquiv K (BinaryTensorFactors E V)
  let q' := q.comp e.toLinearMap
  let pair (F : ℝ → Submodule K E) (G : ℝ → Submodule K V) :
      ∀ i, ℝ → Submodule K (BinaryTensorFactors E V i) := fun i ↦ match i with
    | .inl _ => F
    | .inr _ => G
  have hvalue (H : ∀ i, ℝ → Submodule K (BinaryTensorFactors E V i)) :
      filtrationExpectation (fun t ↦ (piTensorFiltration H t).map q') =
        filtrationExpectation (fun t ↦ (tensorFiltration (H (.inl ())) (H (.inr ())) t).map q) := by
    dsimp only [q', e]
    simp_rw [map_comp, piTensorFiltration_map_binaryTensorEquiv]
  have ha : ∀ i, 0 < finrank K (BinaryTensorFactors E V i) := by
    rintro (⟨⟩ | ⟨⟩)
    · exact hE
    · exact hV
  obtain ⟨P, hP, hPE, hneg, hmin⟩ := exists_normalized_quotient_optimizer q'
    (hq.comp e.surjective) ha (pair F₀ G₀)
    (by
      rintro (⟨⟩ | ⟨⟩)
      · exact hF₀
      · exact hG₀)
    (by dsimp only; rw [hvalue]; exact hneg₀)
  dsimp only at hneg
  rw [hvalue] at hneg
  simp only [Fintype.sum_sum_type, Fintype.sum_unique] at hPE
  refine ⟨P (.inl ()), P (.inr ()), hP (.inl ()), hP (.inr ()), hPE, hneg, ?_⟩
  intro F G hF hG hpos
  have hh := hmin (pair F G)
    (by
      rintro (⟨⟩ | ⟨⟩)
      · exact hF
      · exact hG)
    (by simpa only [Fintype.sum_sum_type, Fintype.sum_unique] using hpos)
  dsimp only at hh
  rw [hvalue, hvalue] at hh
  simpa only [Fintype.sum_sum_type, Fintype.sum_unique] using hh

end Binary

section BinaryAcrossUniverses

universe wE wV

variable {K : Type*} [Field K] {E : Type wE} {V : Type wV} {Q : Type*}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

set_option quotPrecheck false in
local notation "CenteredE" => (fun F : ℝ → Submodule K E ↦
  Antitone F ∧ (∃ t, F t = ⊥) ∧ (∃ t, F t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) ∧ filtrationExpectation F = 0)
set_option quotPrecheck false in
local notation "CenteredV" => (fun G : ℝ → Submodule K V ↦
  Antitone G ∧ (∃ t, G t = ⊥) ∧ (∃ t, G t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → G s = G t) ∧ filtrationExpectation G = 0)

/-- A centered negative candidate gives an actual centered unit global minimum,
for factors in independent universes. -/
theorem exists_normalized_tensor_quotient_optimizer
    (q : E ⊗[K] V →ₗ[K] Q) (hq : Function.Surjective q)
    (hE : 0 < finrank K E) (hV : 0 < finrank K V)
    (F₀ : ℝ → Submodule K E) (G₀ : ℝ → Submodule K V)
    (hF₀ : CenteredE F₀) (hG₀ : CenteredV G₀)
    (hneg₀ : filtrationExpectation (fun t ↦ (tensorFiltration F₀ G₀ t).map q) < 0) :
    ∃ (P : ℝ → Submodule K E) (R : ℝ → Submodule K V),
      CenteredE P ∧ CenteredV R ∧ filtrationPairing P P + filtrationPairing R R = 1 ∧
      filtrationExpectation (fun t ↦ (tensorFiltration P R t).map q) < 0 ∧
      ∀ (F : ℝ → Submodule K E) (G : ℝ → Submodule K V),
        CenteredE F → CenteredV G → 0 < filtrationPairing F F + filtrationPairing G G →
        filtrationExpectation (fun t ↦ (tensorFiltration P R t).map q) ≤
          filtrationExpectation (fun t ↦ (tensorFiltration F G t).map q) /
            Real.sqrt (filtrationPairing F F + filtrationPairing G G) := by
  let e : ULift.{wV} E ≃ₗ[K] E := ULift.moduleEquiv
  let d : ULift.{wE} V ≃ₗ[K] V := ULift.moduleEquiv
  let q' := q.comp (TensorProduct.congr e d).toLinearMap
  have hvalue (F : ℝ → Submodule K (ULift.{wV} E))
      (G : ℝ → Submodule K (ULift.{wE} V)) :
      filtrationExpectation (fun t ↦ (tensorFiltration F G t).map q') =
        filtrationExpectation (fun t ↦ (tensorFiltration
          (fun s ↦ (F s).map e.toLinearMap) (fun s ↦ (G s).map d.toLinearMap) t).map q) := by
    congr 1
    funext t
    change (tensorFiltration F G t).map (q.comp (TensorProduct.map e.toLinearMap d.toLinearMap)) = _
    rw [map_comp, tensorFiltration_map]
  have he (F : ℝ → Submodule K E) :
      (fun t ↦ ((F t).map e.symm.toLinearMap).map e.toLinearMap) = F := by
    funext t
    rw [← map_comp, e.comp_symm, map_id]
  have hd (G : ℝ → Submodule K V) :
      (fun t ↦ ((G t).map d.symm.toLinearMap).map d.toLinearMap) = G := by
    funext t
    rw [← map_comp, d.comp_symm, map_id]
  obtain ⟨P, R, hP, hR, hunit, hneg, hmin⟩ :=
    exists_normalized_tensor_quotient_optimizer_sameUniverse q'
      (hq.comp (TensorProduct.congr e d).surjective)
      (by simpa only [e.finrank_eq] using hE) (by simpa only [d.finrank_eq] using hV)
      (fun t ↦ (F₀ t).map e.symm.toLinearMap) (fun t ↦ (G₀ t).map d.symm.toLinearMap)
      (centered_filtration_map_equiv e.symm F₀ hF₀)
      (centered_filtration_map_equiv d.symm G₀ hG₀)
      (by rw [hvalue, he, hd]; exact hneg₀)
  refine ⟨fun t ↦ (P t).map e.toLinearMap, fun t ↦ (R t).map d.toLinearMap,
    centered_filtration_map_equiv e P hP, centered_filtration_map_equiv d R hR,
    ?_, (hvalue P R).symm.trans_lt hneg, ?_⟩
  · simpa only [filtrationPairing_map_equiv] using hunit
  · intro F G hF hG hpos
    have hh := hmin (fun t ↦ (F t).map e.symm.toLinearMap)
      (fun t ↦ (G t).map d.symm.toLinearMap)
      (centered_filtration_map_equiv e.symm F hF)
      (centered_filtration_map_equiv d.symm G hG)
      (by simpa only [filtrationPairing_map_equiv] using hpos)
    simpa only [hvalue, he, hd, filtrationPairing_map_equiv] using hh

end BinaryAcrossUniverses

end Submodule

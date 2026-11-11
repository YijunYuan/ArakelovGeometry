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
public import Mathlib.Algebra.Order.GroupWithZero.Finset

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

theorem filtrationWeightEnergy_mul (a : J → ℕ) (w : ∀ j, Fin (a j) → ℝ) (t : ℝ) :
    filtrationWeightEnergy a (fun j i ↦ t * w j i) = t ^ 2 * filtrationWeightEnergy a w := by
  simp only [filtrationWeightEnergy, mul_pow, ← Finset.mul_sum, mul_div_assoc]

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

end Submodule

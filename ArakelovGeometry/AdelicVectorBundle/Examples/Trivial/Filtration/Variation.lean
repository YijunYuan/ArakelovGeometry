/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.Pairing
public import ArakelovGeometry.LinearAlgebra.Filtration.Lift
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.CommonAdaptedBasis
public import Mathlib.Analysis.Real.Sqrt

/-!
# Normalization and variation in a fixed common basis

The operations below translate cuts or change the weights of one specified basis.
No vector space structure on the set of filtrations is asserted.
-/

@[expose] public section

open Module

namespace Submodule

variable {K E ι : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite ι]

/-- The filtration norm is the square root of intrinsic self-pairing. -/
noncomputable def filtrationNorm (F : ℝ → Submodule K E) : ℝ :=
  Real.sqrt (filtrationPairing F F)

/-- Center a filtration by its mean weight. -/
noncomputable def filtrationCenter (F : ℝ → Submodule K E) (t : ℝ) : Submodule K E :=
  F (t + filtrationExpectation F)

/-- Vary the weights of a specified basis; the choice of basis is part of this operation. -/
noncomputable def weightedBasisVariation (b : Basis ι K E) (a c : ι → ℝ) (ε t : ℝ) :
    Submodule K E := span K (b '' {i | t ≤ a i + ε * c i})

variable (b : Basis ι K E) (a c : ι → ℝ) {F G : ℝ → Submodule K E}
  (hF : ∀ t, F t = span K (b '' {i | t ≤ a i}))
  (hG : ∀ t, G t = span K (b '' {i | t ≤ c i}))

include hF hG in
omit [FiniteDimensional K E] in
theorem filtrationPairing_comm_of_common_basis : filtrationPairing F G = filtrationPairing G F := by
  classical
  let := Fintype.ofFinite ι
  rw [filtrationPairing_eq_sum_weights b a c hF hG,
    filtrationPairing_eq_sum_weights b c a hG hF]
  simp only [mul_comm]

include hF

omit [FiniteDimensional K E] in
theorem filtrationSelfPairing_nonneg : 0 ≤ filtrationPairing F F := by
  classical
  let := Fintype.ofFinite ι
  rw [filtrationPairing_eq_sum_weights b a a hF hF]
  exact div_nonneg (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (a i)) (Nat.cast_nonneg _)

omit [FiniteDimensional K E] in
theorem filtrationSelfPairing_eq_zero_iff_weights (hdim : 0 < finrank K E) :
    filtrationPairing F F = 0 ↔ ∀ i, a i = 0 := by
  classical
  let := Fintype.ofFinite ι
  rw [filtrationPairing_eq_sum_weights b a a hF hF,
    div_eq_zero_iff, or_iff_left (ne_of_gt (Nat.cast_pos.mpr hdim))]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ mul_self_nonneg (a i))]
  simp only [Finset.mem_univ, true_implies, mul_self_eq_zero]

omit [FiniteDimensional K E] [Finite ι] in
/-- The zero weights describe exactly the trivial filtration. -/
theorem weights_eq_zero_iff_trivial : (∀ i, a i = 0) ↔
    ∀ t, F t = if t ≤ 0 then ⊤ else ⊥ := by
  classical
  constructor
  · intro ha t
    rw [hF]
    simp only [ha]
    split_ifs with ht
    · simpa only [ht, Set.ofPred_true, Set.image_univ] using b.span_eq
    · simp [ht]
  · intro ht i
    have hmem (t : ℝ) : b i ∈ F t ↔ t ≤ a i := by
      rw [hF]
      simp [b.mem_span_image]
    have hnonneg : 0 ≤ a i := (hmem 0).mp (by simp [ht])
    have hnonpos : a i ≤ 0 := by
      by_contra hn
      have hm := (hmem (a i)).mpr le_rfl
      rw [ht, ite_eq_right hn, mem_bot] at hm
      exact b.ne_zero i hm
    exact le_antisymm hnonpos hnonneg

omit [FiniteDimensional K E] in
theorem filtrationNorm_sq : filtrationNorm F ^ 2 = filtrationPairing F F := by
  exact Real.sq_sqrt (filtrationSelfPairing_nonneg b a hF)

omit [FiniteDimensional K E] in
theorem filtrationNorm_eq_zero_iff_trivial (hdim : 0 < finrank K E) :
    filtrationNorm F = 0 ↔ ∀ t, F t = if t ≤ 0 then ⊤ else ⊥ := by
  rw [filtrationNorm, Real.sqrt_eq_zero (filtrationSelfPairing_nonneg b a hF),
    filtrationSelfPairing_eq_zero_iff_weights b a hF hdim,
    weights_eq_zero_iff_trivial b a hF]

omit [FiniteDimensional K E] [Finite ι] in
theorem filtrationCenter_eq_span_weights (t : ℝ) :
    filtrationCenter F t = span K (b '' {i | t ≤ a i - filtrationExpectation F}) := by
  rw [filtrationCenter, hF]
  congr 2
  ext i
  exact le_sub_iff_add_le.symm

theorem filtrationExpectation_center : filtrationExpectation (filtrationCenter F) = 0 := by
  classical
  let := Fintype.ofFinite ι
  rw [filtrationExpectation_eq_sum_weights b _ (filtrationCenter_eq_span_weights b a hF)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    filtrationExpectation_eq_sum_weights b a hF, ← finrank_eq_card_basis b]
  by_cases hd : (finrank K E : ℝ) = 0
  · simp [hd]
  · field_simp
    ring

theorem filtrationSelfPairing_center :
    filtrationPairing (filtrationCenter F) (filtrationCenter F) =
      filtrationPairing F F - filtrationExpectation F ^ 2 := by
  classical
  let := Fintype.ofFinite ι
  rw [filtrationPairing_eq_sum_weights b _ _
    (filtrationCenter_eq_span_weights b a hF) (filtrationCenter_eq_span_weights b a hF),
    filtrationPairing_eq_sum_weights b a a hF hF,
    filtrationExpectation_eq_sum_weights b a hF]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    ← finrank_eq_card_basis b]
  by_cases hd : (finrank K E : ℝ) = 0
  · simp [hd]
  · field_simp
    ring

omit hF

omit [FiniteDimensional K E] [Finite ι] in
theorem weightedBasisVariation_antitone (ε : ℝ) : Antitone (weightedBasisVariation b a c ε) :=
  antitone_span_weights b (fun i ↦ a i + ε * c i)

omit [FiniteDimensional K E] in
theorem weightedBasisVariation_attains_bot_top (ε : ℝ) :
    (∃ t, weightedBasisVariation b a c ε t = ⊥) ∧
      (∃ t, weightedBasisVariation b a c ε t = ⊤) :=
  span_weights_attains_bot_top b (fun i ↦ a i + ε * c i)

omit [FiniteDimensional K E] in
theorem weightedBasisVariation_locallyConstant_left (ε t : ℝ) :
    ∃ δ > 0, ∀ s, t - δ < s → s ≤ t →
      weightedBasisVariation b a c ε s = weightedBasisVariation b a c ε t :=
  span_weights_locallyConstant_left b (fun i ↦ a i + ε * c i) t

include hF hG in
theorem filtrationExpectation_weightedBasisVariation (ε : ℝ) :
    filtrationExpectation (weightedBasisVariation b a c ε) =
      filtrationExpectation F + ε * filtrationExpectation G := by
  classical
  let := Fintype.ofFinite ι
  rw [filtrationExpectation_eq_sum_weights (F := weightedBasisVariation b a c ε)
    b (fun i ↦ a i + ε * c i) (fun _ ↦ rfl),
    filtrationExpectation_eq_sum_weights b a hF,
    filtrationExpectation_eq_sum_weights b c hG]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc]

include hF hG in
omit [FiniteDimensional K E] in
theorem filtrationPairing_weightedBasisVariation_self (ε : ℝ) :
    filtrationPairing (weightedBasisVariation b a c ε) (weightedBasisVariation b a c ε) =
      filtrationPairing F F + 2 * ε * filtrationPairing F G +
        ε ^ 2 * filtrationPairing G G := by
  classical
  let := Fintype.ofFinite ι
  rw [filtrationPairing_eq_sum_weights (F := weightedBasisVariation b a c ε)
    (G := weightedBasisVariation b a c ε) b (fun i ↦ a i + ε * c i)
    (fun i ↦ a i + ε * c i) (fun _ ↦ rfl) (fun _ ↦ rfl),
    filtrationPairing_eq_sum_weights b a a hF hF,
    filtrationPairing_eq_sum_weights b a c hF hG,
    filtrationPairing_eq_sum_weights b c c hG hG]
  have hexpand (i : ι) : (a i + ε * c i) * (a i + ε * c i) =
      a i * a i + (2 * ε) * (a i * c i) + ε ^ 2 * (c i * c i) := by ring
  simp only [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc]

omit [Finite ι] in
/-- Positivity for every genuine finite real filtration, using the A3 basis producer. -/
theorem filtrationPairing_self_nonneg (F : ℝ → Submodule K E)
    (hanti : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    0 ≤ filtrationPairing F F := by
  obtain ⟨b, a, _, hFa, _, _, _⟩ := exists_common_weighted_basis
    hanti hbot htop hleft hanti hbot htop hleft
  exact filtrationSelfPairing_nonneg b a hFa

omit [Finite ι] in
theorem filtrationNorm_eq_zero_iff (F : ℝ → Submodule K E)
    (hanti : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hdim : 0 < finrank K E) :
    filtrationNorm F = 0 ↔ ∀ t, F t = if t ≤ 0 then ⊤ else ⊥ := by
  obtain ⟨b, a, _, hFa, _, _, _⟩ := exists_common_weighted_basis
    hanti hbot htop hleft hanti hbot htop hleft
  exact filtrationNorm_eq_zero_iff_trivial b a hFa hdim

omit [Finite ι] in
/-- Translating by the mean preserves all the real-filtration axioms and has mean zero. -/
theorem filtrationCenter_properties (F : ℝ → Submodule K E)
    (hanti : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    Antitone (filtrationCenter F) ∧
      (∃ t, filtrationCenter F t = ⊥) ∧ (∃ t, filtrationCenter F t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t →
        filtrationCenter F s = filtrationCenter F t) ∧
      filtrationExpectation (filtrationCenter F) = 0 := by
  obtain ⟨b, a, _, hFa, _, _, _⟩ := exists_common_weighted_basis
    hanti hbot htop hleft hanti hbot htop hleft
  have hc : filtrationCenter F = fun t ↦
      span K (b '' {i | t ≤ a i - filtrationExpectation F}) :=
    funext (filtrationCenter_eq_span_weights b a hFa)
  refine ⟨?_, ?_, ?_, ?_, filtrationExpectation_center b a hFa⟩
  · rw [hc]
    exact antitone_span_weights b _
  · rw [hc]
    exact (span_weights_attains_bot_top b _).1
  · rw [hc]
    exact (span_weights_attains_bot_top b _).2
  · rw [hc]
    exact span_weights_locallyConstant_left b _

end Submodule

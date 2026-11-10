/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Lattice counts from averaging over an actual fundamental domain -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace ArakelovGeometry.LatticeCount

/-- Translating one point of a fibre to zero injects that fibre into the actual
finite difference set in the original subgroup. -/
theorem tsum_indicator_translate_le_card
    {E : Type*} [AddCommGroup E] (L : AddSubgroup E) (S D : Set E)
    (hD : {l : L | (l : E) ∈ D}.Finite)
    (hdiff : ∀ s ∈ S, ∀ t ∈ S, s - t ∈ D) (x : E) :
    (∑' l : L, S.indicator (fun _ => (1 : ℝ≥0∞)) ((l : E) + x)) ≤
      (Nat.card {l : L | (l : E) ∈ D} : ℝ≥0∞) := by
  classical
  let T : Set L := {l | (l : E) + x ∈ S}
  by_cases hT : T.Nonempty
  · obtain ⟨l₀, hl₀⟩ := hT
    let f : T → {l : L | (l : E) ∈ D} := fun l =>
      ⟨l.val - l₀, by simpa using hdiff _ l.property _ hl₀⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      simpa [f] using congrArg (fun l : L => l + l₀) (congrArg Subtype.val hab)
    let := hD.fintype
    let : Finite T := Finite.of_injective f hf
    have hc := Nat.card_le_card_of_injective f hf
    have heq : (∑' l : L, S.indicator (fun _ => (1 : ℝ≥0∞)) ((l : E) + x)) =
        (Nat.card T : ℝ≥0∞) := by
      change (∑' l : L, T.indicator (fun _ => (1 : ℝ≥0∞)) l) = _
      rw [← tsum_subtype T (fun _ => (1 : ℝ≥0∞)), ENNReal.tsum_one,
        ENat.card_eq_coe_natCard]
      rfl
    rw [heq]
    exact_mod_cast hc
  · have hz (l : L) : S.indicator (fun _ => (1 : ℝ≥0∞)) ((l : E) + x) = 0 := by
      have hm : (l : E) + x ∉ S := fun hs => hT ⟨l, hs⟩
      simp [hm]
    simp only [hz, tsum_zero]
    exact bot_le

/-- The actual fundamental-domain decomposition and nonnegative Tonelli averaging
turn the fibre injection into a measure bound. -/
theorem measure_le_card_mul_fundamentalDomain
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ] (L : AddSubgroup E) [Countable L]
    {F S D : Set E} (hF : IsAddFundamentalDomain L F μ) (hS : MeasurableSet S)
    (hD : {l : L | (l : E) ∈ D}.Finite)
    (hdiff : ∀ s ∈ S, ∀ t ∈ S, s - t ∈ D) :
    μ S ≤ (Nat.card {l : L | (l : E) ∈ D} : ℝ≥0∞) * μ F := by
  classical
  calc
    μ S = ∫⁻ x, S.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
      simp [hS]
    _ = ∑' l : L, ∫⁻ x in F,
        S.indicator (fun _ => (1 : ℝ≥0∞)) (l +ᵥ x) ∂μ :=
      hF.lintegral_eq_tsum'' _
    _ = ∫⁻ x in F, ∑' l : L,
        S.indicator (fun _ => (1 : ℝ≥0∞)) (l +ᵥ x) ∂μ := by
      symm
      apply lintegral_tsum
      intro l
      exact ((measurable_const.indicator hS).comp
        (continuous_const.add continuous_id).measurable).aemeasurable
    _ ≤ ∫⁻ _ in F, (Nat.card {l : L | (l : E) ∈ D} : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro x
      exact tsum_indicator_translate_le_card L S D hD hdiff x
    _ = _ := by simp

/-- Bounded subsets meet a closed discrete subgroup in finitely many actual points. -/
theorem finite_subgroup_points_of_bounded
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (L : AddSubgroup E) [DiscreteTopology L] {D : Set E}
    (hD : Bornology.IsBounded D) : {l : L | (l : E) ∈ D}.Finite := by
  have hf : (D ∩ (L : Set E)).Finite := by
    have hd : IsDiscrete (L : Set E) := DiscreteTopology.isDiscrete
    exact Metric.finite_isBounded_inter_isClosed hd hD AddSubgroup.isClosed_of_discreteTopology
  apply hf.of_injOn (f := fun l : L => (l : E)) ?_ Subtype.val_injective.injOn
  intro l hl
  exact ⟨hl, l.property⟩

/-- The actual count in a bounded symmetric convex set controls its Haar measure,
with the geometric factor `2 ^ finrank` and its original fundamental-domain measure. -/
theorem measure_le_two_pow_card_mul_fundamentalDomain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    (L : AddSubgroup E) [Countable L] [DiscreteTopology L] {F D : Set E}
    (hF : IsAddFundamentalDomain L F μ) (hD : MeasurableSet D)
    (hbounded : Bornology.IsBounded D) (hconvex : Convex ℝ D)
    (hsymm : ∀ x ∈ D, -x ∈ D) :
    μ D ≤ 2 ^ Module.finrank ℝ E * (Nat.card {l : L | (l : E) ∈ D} : ℝ≥0∞) * μ F := by
  have hdiff : ∀ s ∈ (2⁻¹ : ℝ) • D, ∀ t ∈ (2⁻¹ : ℝ) • D, s - t ∈ D := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [sub_eq_add_neg, ← smul_neg]
    exact hconvex hs (hsymm _ ht) (by norm_num) (by norm_num) (by norm_num)
  have hcount := measure_le_card_mul_fundamentalDomain L hF
    (hD.const_smul_of_ne_zero (by norm_num : (2⁻¹ : ℝ) ≠ 0))
    (finite_subgroup_points_of_bounded L hbounded) hdiff
  have hscale : 2 ^ Module.finrank ℝ E * μ ((2⁻¹ : ℝ) • D) = μ D := by
    rw [Measure.addHaar_smul_of_nonneg μ (by norm_num : 0 ≤ (2⁻¹ : ℝ)) D,
      ENNReal.ofReal_pow (by norm_num : 0 ≤ (2⁻¹ : ℝ)),
      ENNReal.ofReal_inv_of_pos zero_lt_two]
    norm_num only [ENNReal.ofReal_ofNat]
    rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
      one_pow, one_mul]
  rw [← hscale]
  calc
    _ ≤ 2 ^ Module.finrank ℝ E *
        ((Nat.card {l : L | (l : E) ∈ D} : ℝ≥0∞) * μ F) :=
      by gcongr
    _ = _ := (mul_assoc _ _ _).symm

/-- Convex frontiers have zero Haar measure, so the actual interior-point count
already controls the whole body's volume, including in dimension zero. -/
theorem measure_le_two_pow_card_interior_mul_fundamentalDomain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    (L : AddSubgroup E) [Countable L] [DiscreteTopology L] {F C : Set E}
    (hF : IsAddFundamentalDomain L F μ) (hbounded : Bornology.IsBounded C)
    (hconvex : Convex ℝ C) (hsymm : ∀ x ∈ C, -x ∈ C) :
    μ C ≤ 2 ^ Module.finrank ℝ E *
      (Nat.card {l : L | (l : E) ∈ interior C} : ℝ≥0∞) * μ F := by
  have hpre : (Homeomorph.neg E) ⁻¹' C = C := by
    ext x
    change -x ∈ C ↔ x ∈ C
    exact ⟨fun hx => by simpa using hsymm (-x) hx, hsymm x⟩
  have hsymmI (x : E) (hx : x ∈ interior C) : -x ∈ interior C := by
    change x ∈ (Homeomorph.neg E) ⁻¹' interior C
    rw [(Homeomorph.neg E).preimage_interior, hpre]
    exact hx
  rw [← measure_interior_of_null_frontier (hconvex.addHaar_frontier μ)]
  exact measure_le_two_pow_card_mul_fundamentalDomain L hF isOpen_interior.measurableSet
    (hbounded.subset interior_subset) hconvex.interior hsymmI

end ArakelovGeometry.LatticeCount

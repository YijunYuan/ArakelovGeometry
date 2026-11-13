/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic
public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Ordered

import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.ExactSequence
import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Dual
import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Majorant
import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.ExactSequence
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Restriction
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Discrepancy upper bounds for actual general ordered slopes

An actual quotient approximates the source minimum from above. Actual
restriction slope comparisons bound the kernel's ordered sum and account
for the omitted slots by the actual ambient minimum. Exact-sequence
discrepancy bounds then permit induction on the true dimension.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]

/-- The literal source infimum produces a genuine positive-rank quotient
whose actual maximum is below any strict real upper bound for the minimum.
Rank-nullity proves that its kernel has smaller rank, and its actual
ordinary degree is bounded through the actual quotient mean. -/
theorem exists_quotient_maximalSlope_lt_of_minimalSlope_lt
    (c : ℝ) (hc : V.minimalSlope < (c : EReal)) :
    ∃ U : Submodule K V, 0 < Module.finrank K (V ⧸ U) ∧
      Module.finrank K U < Module.finrank K V ∧
      (V.quotientOfNormMeasurability U).maximalSlope < (c : EReal) ∧
      (V.quotientOfNormMeasurability U).degree ≤
        (Module.finrank K (V ⧸ U) : ℝ) * c := by
  change (⨅ U : {U : Submodule K V // 0 < Module.finrank K (V ⧸ U)},
    (V.quotientOfNormMeasurability U.val).maximalSlope) < (c : EReal) at hc
  obtain ⟨U, hU⟩ := iInf_lt_iff.mp hc
  have hr := U.val.finrank_quotient_add_finrank
  have hm := (V.quotientOfNormMeasurability U.val).slope_le_maximalSlope U.property
  have hmean : (V.quotientOfNormMeasurability U.val).slope < c :=
    EReal.coe_lt_coe_iff.mp (hm.trans_lt hU)
  refine ⟨U.val, U.property, by omega, hU, ?_⟩
  rw [degree_eq_rank_mul_slope]
  exact mul_le_mul_of_nonneg_left hmean.le (Nat.cast_nonneg _)

/-- Actual restriction slot comparisons and the ambient minimum account
for every omitted ambient slot by one quotient-rank copy of a real lower bound. -/
theorem sum_hnSlope_restrict_add_quotient_rank_mul_le
    (U : Submodule K V) (b : ℝ) (hb : (b : EReal) ≤ V.minimalSlope) :
    (∑ j, (V.restrictOfNormMeasurability U).hnSlope j) +
      (Module.finrank K (V ⧸ U) : ℝ) * b ≤ ∑ j, V.hnSlope j := by
  classical
  let e := Fin.castLE U.finrank_le
  have hn : ∀ j, 0 ≤ V.hnSlope j - b := by
    intro j
    exact sub_nonneg.mpr (EReal.coe_le_coe_iff.mp
      (hb.trans (V.minimalSlope_le_hnSlope j)))
  have hsum :
      (∑ j, ((V.restrictOfNormMeasurability U).hnSlope j - b)) ≤
        ∑ j : Fin (Module.finrank K U), (V.hnSlope (e j) - b) := by
    apply Finset.sum_le_sum
    intro j _
    exact sub_le_sub_right (V.hnSlope_restrict_le U j) b
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.univ.image e)) (fun j _ _ ↦ hn j)
  rw [Finset.sum_image (Fin.castLE_injective U.finrank_le).injOn] at hsub
  have hs := hsum.trans hsub
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  have hr : (Module.finrank K (V ⧸ U) : ℝ) + (Module.finrank K U : ℝ) =
      (Module.finrank K V : ℝ) := by exact_mod_cast U.finrank_quotient_add_finrank
  rw [← hr, add_mul] at hs
  linarith

private theorem degree_sub_majorantDiscrepancy_le_sum_hnSlope_aux (r : ℕ) :
    ∀
      (W : AdelicVectorBundle S), Module.finrank K W = r →
      (W.degree : EReal) - W.majorantDiscrepancy ≤
        ((∑ j, W.hnSlope j) : ℝ) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro W hr
    by_cases hz : Module.finrank K W = 0
    · let : IsEmpty (Fin (Module.finrank K W)) := by rw [hz]; infer_instance
      rw [W.degree_eq_zero_of_finrank_eq_zero hz,
        W.majorantDiscrepancy_eq_zero_of_finrank_eq_zero hz]
      simp
    have hp : 0 < Module.finrank K W := Nat.pos_of_ne_zero hz
    by_cases hD : W.majorantDiscrepancy = ⊤
    · rw [hD, EReal.sub_top]
      exact bot_le
    obtain ⟨d, hd⟩ : ∃ d : ℝ, W.majorantDiscrepancy = (d : EReal) := by
      lift W.majorantDiscrepancy to ℝ using
        ⟨hD, (W.bot_lt_majorantDiscrepancy).ne'⟩ with d
      exact ⟨d, rfl⟩
    rw [hd, ← EReal.coe_sub]
    apply EReal.coe_le_coe
    obtain ⟨b, hb⟩ := W.exists_minimalSlope_eq_coe hp
    apply le_of_forall_pos_le_add
    intro η hη
    let ε := η / (Module.finrank K W : ℝ)
    have hpos : 0 < (Module.finrank K W : ℝ) := Nat.cast_pos.mpr hp
    have hε : 0 < ε := div_pos hη hpos
    have hc : W.minimalSlope < ((b + ε : ℝ) : EReal) := by
      rw [hb]
      apply EReal.coe_lt_coe
      linarith
    obtain ⟨U, hQ, hU, hmax, hdegQ⟩ :=
      W.exists_quotient_maximalSlope_lt_of_minimalSlope_lt (b + ε) hc
    have hUr : Module.finrank K U < r := by simpa only [hr] using hU
    have hDU : (W.restrictOfNormMeasurability U).majorantDiscrepancy ≠ ⊤ :=
      ne_of_lt ((W.majorantDiscrepancy_restrict_le U).trans_lt
        (lt_top_iff_ne_top.mpr hD))
    obtain ⟨du, hdu⟩ : ∃ du : ℝ,
        (W.restrictOfNormMeasurability U).majorantDiscrepancy = (du : EReal) := by
      lift (W.restrictOfNormMeasurability U).majorantDiscrepancy to ℝ using
        ⟨hDU, ((W.restrictOfNormMeasurability U).bot_lt_majorantDiscrepancy).ne'⟩ with du
      exact ⟨du, rfl⟩
    have hi := ih (Module.finrank K U) hUr (W.restrictOfNormMeasurability U) rfl
    rw [hdu, ← EReal.coe_sub] at hi
    have hi' := EReal.coe_le_coe_iff.mp hi
    have hdrop : (W.degree : EReal) +
        (W.restrictOfNormMeasurability U).majorantDiscrepancy ≤
      (W.degree : EReal) +
        (W.restrictOfNormMeasurability U).majorantDiscrepancy +
          (W.quotientOfNormMeasurability U).majorantDiscrepancy := by
      simpa only [add_zero] using add_le_add_right
        ((W.quotientOfNormMeasurability U).majorantDiscrepancy_nonneg)
        ((W.degree : EReal) +
          (W.restrictOfNormMeasurability U).majorantDiscrepancy)
    have hs := hdrop.trans (W.degree_add_majorantDiscrepancy_restrict_add_quotient_le U)
    rw [hd, hdu] at hs
    simp only [← EReal.coe_add, EReal.coe_le_coe_iff] at hs
    have htail := W.sum_hnSlope_restrict_add_quotient_rank_mul_le U b hb.ge
    have hqle : Module.finrank K (W ⧸ U) ≤ Module.finrank K W := by
      have h := U.finrank_quotient_add_finrank
      omega
    have hqle' : (Module.finrank K (W ⧸ U) : ℝ) ≤ (Module.finrank K W : ℝ) :=
      Nat.cast_le.mpr hqle
    have heq : ε * (Module.finrank K W : ℝ) = η := div_mul_cancel₀ η hpos.ne'
    have herr : (Module.finrank K (W ⧸ U) : ℝ) * ε ≤ η := by
      calc
        _ ≤ (Module.finrank K W : ℝ) * ε := mul_le_mul_of_nonneg_right hqle' hε.le
        _ = η := by rw [mul_comm]; exact heq
    rw [mul_add] at hdegQ
    linarith

/-- Actual degree minus capital discrepancy is at most the sum of actual
general ordered slopes. Infinite capital discrepancy is handled directly
as a negative-infinite left side, before any real lift or subtraction. -/
theorem degree_sub_majorantDiscrepancy_le_sum_hnSlope :
    (V.degree : EReal) - V.majorantDiscrepancy ≤
      ((∑ j, V.hnSlope j) : ℝ) :=
  degree_sub_majorantDiscrepancy_le_sum_hnSlope_aux
    (Module.finrank K V) V rfl

/-- Source inequality (4.68) with the actual global capital discrepancy,
including its positive-infinite branch and the empty rank-zero sum. -/
theorem degree_le_sum_hnSlope_add_majorantDiscrepancy :
    (V.degree : EReal) ≤
      ((∑ j, V.hnSlope j) : ℝ) + V.majorantDiscrepancy := by
  by_cases hD : V.majorantDiscrepancy = ⊤
  · rw [hD, EReal.coe_add_top]
    exact le_top
  obtain ⟨d, hd⟩ : ∃ d : ℝ, V.majorantDiscrepancy = (d : EReal) := by
    lift V.majorantDiscrepancy to ℝ using
      ⟨hD, (V.bot_lt_majorantDiscrepancy).ne'⟩ with d
    exact ⟨d, rfl⟩
  have h := V.degree_sub_majorantDiscrepancy_le_sum_hnSlope
  rw [hd, ← EReal.coe_sub] at h
  rw [hd, ← EReal.coe_add]
  apply EReal.coe_le_coe
  have hr := EReal.coe_le_coe_iff.mp h
  linarith

private theorem degree_sub_determinantDiscrepancy_le_sum_hnSlope_aux (r : ℕ) :
    ∀
      (W : AdelicVectorBundle S), Module.finrank K W = r →
        W.toNormFamily.IsUltrametricAtFinitePlaces →
      W.degree - W.determinantDiscrepancy ≤ ∑ j, W.hnSlope j := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro W hr hW
    by_cases hz : Module.finrank K W = 0
    · let : IsEmpty (Fin (Module.finrank K W)) := by rw [hz]; infer_instance
      rw [W.degree_eq_zero_of_finrank_eq_zero hz,
        W.determinantDiscrepancy_eq_zero_of_finrank_eq_zero hz]
      simp
    have hp : 0 < Module.finrank K W := Nat.pos_of_ne_zero hz
    obtain ⟨b, hb⟩ := W.exists_minimalSlope_eq_coe hp
    apply le_of_forall_pos_le_add
    intro η hη
    let ε := η / (Module.finrank K W : ℝ)
    have hpos : 0 < (Module.finrank K W : ℝ) := Nat.cast_pos.mpr hp
    have hε : 0 < ε := div_pos hη hpos
    have hc : W.minimalSlope < ((b + ε : ℝ) : EReal) := by
      rw [hb]
      apply EReal.coe_lt_coe
      linarith
    obtain ⟨U, hQ, hU, hmax, hdegQ⟩ :=
      W.exists_quotient_maximalSlope_lt_of_minimalSlope_lt (b + ε) hc
    have hUr : Module.finrank K U < r := by simpa only [hr] using hU
    have hWU : (W.restrictOfNormMeasurability U).toNormFamily.IsUltrametricAtFinitePlaces := by
      simpa only [restrictOfNormMeasurability_toNormFamily] using hW.restrict U
    have hi := ih (Module.finrank K U) hUr (W.restrictOfNormMeasurability U) rfl hWU
    have hs := W.degree_sub_determinantDiscrepancy_le_restrict_add_quotient U (hV := hW)
    have hn := (W.quotientOfNormMeasurability U).determinantDiscrepancy_nonneg
    have htail := W.sum_hnSlope_restrict_add_quotient_rank_mul_le U b hb.ge
    have hqle : Module.finrank K (W ⧸ U) ≤ Module.finrank K W := by
      have h := U.finrank_quotient_add_finrank
      omega
    have hqle' : (Module.finrank K (W ⧸ U) : ℝ) ≤ (Module.finrank K W : ℝ) :=
      Nat.cast_le.mpr hqle
    have heq : ε * (Module.finrank K W : ℝ) = η := div_mul_cancel₀ η hpos.ne'
    have herr : (Module.finrank K (W ⧸ U) : ℝ) * ε ≤ η := by
      calc
        _ ≤ (Module.finrank K W : ℝ) * ε := mul_le_mul_of_nonneg_right hqle' hε.le
        _ = η := by rw [mul_comm]; exact heq
    rw [mul_add] at hdegQ
    linarith

/-- Source inequality (4.69) in corrected form, with the actual
finite-place ultrametric premise and the actual finite determinant discrepancy. -/
theorem degree_sub_determinantDiscrepancy_le_sum_hnSlope
    [hV : V.toNormFamily.IsUltrametricAtFinitePlaces] :
    V.degree - V.determinantDiscrepancy ≤ ∑ j, V.hnSlope j :=
  degree_sub_determinantDiscrepancy_le_sum_hnSlope_aux
    (Module.finrank K V) V rfl hV

/-- Actual determinant discrepancy bounds the ordinary degree above
the full general ordered-slope sum. Zero rank has an empty sum. -/
theorem degree_le_sum_hnSlope_add_determinantDiscrepancy
    [hV : V.toNormFamily.IsUltrametricAtFinitePlaces] :
    V.degree ≤ (∑ j, V.hnSlope j) + V.determinantDiscrepancy := by
  have h := V.degree_sub_determinantDiscrepancy_le_sum_hnSlope
  linarith

/-- Every actual restricted ordered sum is bounded by the ambient sum
of positive parts, by actual slot comparison and nonnegative omitted slots. -/
theorem sum_hnSlope_restrict_le_sum_max (U : Submodule K V) :
    (∑ j, (V.restrictOfNormMeasurability U).hnSlope j) ≤
      ∑ j, max (V.hnSlope j) 0 := by
  classical
  let e := Fin.castLE U.finrank_le
  have hs :
      (∑ j, (V.restrictOfNormMeasurability U).hnSlope j) ≤
        ∑ j : Fin (Module.finrank K U), max (V.hnSlope (e j)) 0 := by
    apply Finset.sum_le_sum
    intro j _
    exact (V.hnSlope_restrict_le U j).trans (le_max_left _ _)
  have ht := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.univ.image e)) (fun j _ _ ↦ le_max_right
      (V.hnSlope j) 0)
  rw [Finset.sum_image (Fin.castLE_injective U.finrank_le).injOn] at ht
  exact hs.trans ht

/-- Source positive-degree inequality (4.70), by testing every actual
restricted degree in the defining supremum. Infinite capital discrepancy
is allowed, and zero rank has an empty positive-part sum. -/
theorem positiveDegree_le_sum_max_hnSlope_add_majorantDiscrepancy :
    V.positiveDegree ≤
      ((∑ j, max (V.hnSlope j) 0) : ℝ) + V.majorantDiscrepancy := by
  apply V.positiveDegree_le
  intro U
  have hd := degree_le_sum_hnSlope_add_majorantDiscrepancy
    (V.restrictOfNormMeasurability U)
  exact hd.trans
    (add_le_add (EReal.coe_le_coe_iff.mpr
      (V.sum_hnSlope_restrict_le_sum_max U))
      (V.majorantDiscrepancy_restrict_le U))

/-- Source positive-degree inequality (4.71) with the true finite-place
ultrametric hypothesis, inherited by every actual restricted norm family. -/
theorem positiveDegree_le_sum_max_hnSlope_add_determinantDiscrepancy
    [hV : V.toNormFamily.IsUltrametricAtFinitePlaces] :
    V.positiveDegree ≤
      (((∑ j, max (V.hnSlope j) 0) + V.determinantDiscrepancy) : ℝ) := by
  apply V.positiveDegree_le
  intro U
  apply EReal.coe_le_coe
  have hVU : (V.restrictOfNormMeasurability U).toNormFamily.IsUltrametricAtFinitePlaces := by
    simpa only [restrictOfNormMeasurability_toNormFamily] using hV.restrict U
  have hd := degree_le_sum_hnSlope_add_determinantDiscrepancy
    (V.restrictOfNormMeasurability U) (hV := hVU)
  have hs := V.sum_hnSlope_restrict_le_sum_max U
  have hδ := V.determinantDiscrepancy_restrict_le U
  linarith

end

end ArakelovGeometry.AdelicVectorBundle

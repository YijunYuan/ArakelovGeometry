/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Ordered

import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Determinant.Bound
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Restriction
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Upper
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Actual first general HN slope and maximal slope

The actual determinant upper bound and sharp dual-degree defect bound
control every actual subspace mean. The maximal-slope supremum then gives
the source logarithmic comparison. Errorfree positive-degree bounds use
the actual maximal slope and include the zero-rank convention.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle.{w} S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

/-- The true determinant correction and actual restriction slot comparison
bound every positive-rank restricted mean by the actual ambient first
ordered slope and the sharp logarithmic rank error. -/
theorem slope_restrict_le_generalHNOrderedSlope_zero_add_log_rank
    [hV : V.toNormFamily.IsUltrametric] (hr : 0 < Module.finrank K V)
    (U : Submodule K V) (hU : 0 < Module.finrank K U) :
    (V.restrictOfMeasurableBase U).slope ≤
      V.generalHNOrderedSlope ⟨0, hr⟩ +
        Real.log (Module.finrank K V) / 2 * (S.v S.Ωinf).toReal := by
  have hVU : (V.restrictOfMeasurableBase U).toNormFamily.IsUltrametric := by
    simpa only [restrictOfMeasurableBase_toNormFamily] using hV.restrict U
  have hd := degree_le_sum_generalHNOrderedSlope_add_determinantDiscrepancy
    (V.restrictOfMeasurableBase U) (hV := hVU)
  have hs : (∑ j, (V.restrictOfMeasurableBase U).generalHNOrderedSlope j) ≤
      (Module.finrank K U : ℝ) * V.generalHNOrderedSlope ⟨0, hr⟩ := by
    calc
      _ ≤ ∑ _j : Fin (Module.finrank K U), V.generalHNOrderedSlope ⟨0, hr⟩ := by
        apply Finset.sum_le_sum
        intro j _
        exact (V.generalHNOrderedSlope_restrict_le U j).trans
          (V.generalHNOrderedSlope_antitone (show
            (⟨0, hr⟩ : Fin (Module.finrank K V)) ≤ Fin.castLE U.finrank_le j from Nat.zero_le _))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hδ := (V.restrictOfMeasurableBase U).degree_add_degree_dual_le
  rw [← determinantDiscrepancy_eq_degree_add_degree_dual
    (V.restrictOfMeasurableBase U)] at hδ
  have hm : 0 < (Module.finrank K U : ℝ) := Nat.cast_pos.mpr hU
  have hl := Real.log_le_log hm (Nat.cast_le.mpr U.finrank_le)
  have hδ' : (V.restrictOfMeasurableBase U).determinantDiscrepancy ≤
      (Module.finrank K U : ℝ) *
        (Real.log (Module.finrank K V) / 2 * (S.v S.Ωinf).toReal) := by
    calc
      _ ≤ (Module.finrank K U : ℝ) / 2 * Real.log (Module.finrank K U) *
          (S.v S.Ωinf).toReal := hδ
      _ ≤ (Module.finrank K U : ℝ) / 2 * Real.log (Module.finrank K V) *
          (S.v S.Ωinf).toReal := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hl (div_nonneg (Nat.cast_nonneg _) (by norm_num)))
        ENNReal.toReal_nonneg
      _ = _ := by ring
  rw [degree_eq_rank_mul_slope] at hd
  apply le_of_mul_le_mul_left (a := (Module.finrank K U : ℝ)) _ hm
  rw [mul_add]
  linarith

/-- Source Remark 4.3.48: the actual maximal-slope supremum is at most
the actual first general ordered slope plus the sharp logarithmic rank
error, with a positive-rank guard before the first slot is formed. -/
theorem maximalSlope_le_generalHNOrderedSlope_zero_add_log_rank
    [hV : V.toNormFamily.IsUltrametric] (hr : 0 < Module.finrank K V) :
    V.maximalSlope ≤
      ((V.generalHNOrderedSlope ⟨0, hr⟩ +
        Real.log (Module.finrank K V) / 2 * (S.v S.Ωinf).toReal) : ℝ) := by
  apply V.maximalSlope_le
  intro U hU
  exact EReal.coe_le_coe_iff.mpr
    (V.slope_restrict_le_generalHNOrderedSlope_zero_add_log_rank hr U hU)

/-- Source errorfree inequality (4.73), with the actual maximal-slope
supremum and explicit rank-zero convention. Its positive part is formed
on the extended real line before multiplication by the true rank. -/
theorem positiveDegree_le_rank_mul_max_maximalSlope :
    V.positiveDegree ≤
      (Module.finrank K V : ℝ) * max (V.maximalSlope) 0 := by
  by_cases hz : Module.finrank K V = 0
  · rw [V.positiveDegree_eq_zero_of_finrank_eq_zero hz,
      V.maximalSlope_eq_bot_of_finrank_eq_zero hz, max_eq_right bot_le]
    simp only [hz, Nat.cast_zero, EReal.coe_zero, zero_mul, le_refl]
  have hp : 0 < Module.finrank K V := Nat.pos_of_ne_zero hz
  obtain ⟨c, hc⟩ := V.exists_maximalSlope_eq_coe hp
  have he : max (c : EReal) 0 = ((max c 0 : ℝ) : EReal) := by
    by_cases h : c ≤ 0
    · have h' : (c : EReal) ≤ 0 := by exact_mod_cast h
      rw [max_eq_right h', max_eq_right h, EReal.coe_zero]
    · have h' : 0 ≤ (c : EReal) := by exact_mod_cast (lt_of_not_ge h).le
      rw [max_eq_left h', max_eq_left (lt_of_not_ge h).le]
  rw [hc, he, ← EReal.coe_mul]
  apply V.positiveDegree_le
  intro U
  apply EReal.coe_le_coe
  by_cases hU : Module.finrank K U = 0
  · rw [degree_eq_zero_of_finrank_eq_zero _ hU]
    exact mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
  have hs := V.slope_restrict_le_maximalSlope U (Nat.pos_of_ne_zero hU)
  rw [hc] at hs
  have hs' := EReal.coe_le_coe_iff.mp hs
  rw [degree_eq_rank_mul_slope]
  exact (mul_le_mul_of_nonneg_left (hs'.trans (le_max_left _ _))
    (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr U.finrank_le) (le_max_right _ _))

/-- Source errorfree inequality (4.72). Positive actual positive degree
forces positive actual maximal slope by the accepted vanishing criterion,
so the positive-part bound becomes the true rank times that maximal slope. -/
theorem positiveDegree_le_rank_mul_maximalSlope_of_pos
    (hV : 0 < V.positiveDegree) :
    V.positiveDegree ≤ (Module.finrank K V : ℝ) * V.maximalSlope := by
  have hm : 0 < V.maximalSlope := lt_of_not_ge fun h ↦ by
    have hz := (V.positiveDegree_eq_zero_iff_maximalSlope_nonpos).mpr h
    rw [hz] at hV
    exact lt_irrefl 0 hV
  simpa only [max_eq_left hm.le] using V.positiveDegree_le_rank_mul_max_maximalSlope

end

end ArakelovGeometry.AdelicVectorBundle

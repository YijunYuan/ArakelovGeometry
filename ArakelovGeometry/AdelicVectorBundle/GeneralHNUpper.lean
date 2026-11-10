/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeneralHNRestriction
import ArakelovGeometry.AdelicVectorBundle.DegreeExactSequenceMajorant
import ArakelovGeometry.AdelicVectorBundle.DegreeExactSequenceDual
import ArakelovGeometry.AdelicVectorBundle.PositiveDegree
import ArakelovGeometry.AdelicVectorBundle.PositiveDegreeExactSequence

/-!
# Discrepancy upper bounds for actual general ordered slopes

An actual quotient approximates the source minimum from above. Actual
restriction slope comparisons bound the kernel's ordered sum and account
for the omitted slots by the actual ambient minimum. Exact-sequence
discrepancy bounds then permit induction on the true dimension.
-/

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The literal source infimum produces a genuine positive-rank quotient
whose actual maximum is below any strict real upper bound for the minimum.
Rank-nullity proves that its kernel has smaller rank, and its actual
ordinary degree is bounded through the actual quotient mean. -/
theorem exists_quotient_maximalSlope_lt_of_minimalSlope_lt
    (c : ℝ) (hc : V.minimalSlope hS hN < (c : EReal)) :
    ∃ U : Submodule K E, 0 < Module.finrank K (E ⧸ U) ∧
      Module.finrank K U < Module.finrank K E ∧
      (V.quotientOfMeasurableBase U hS).maximalSlope hS hN < (c : EReal) ∧
      (V.quotientOfMeasurableBase U hS).degree hS hN ≤
        (Module.finrank K (E ⧸ U) : ℝ) * c := by
  change (⨅ U : {U : Submodule K E // 0 < Module.finrank K (E ⧸ U)},
    (V.quotientOfMeasurableBase U.val hS).maximalSlope hS hN) < (c : EReal) at hc
  obtain ⟨U, hU⟩ := iInf_lt_iff.mp hc
  have hr := U.val.finrank_quotient_add_finrank
  have hm := (V.quotientOfMeasurableBase U.val hS).slope_le_maximalSlope hS hN U.property
  have hmean : (V.quotientOfMeasurableBase U.val hS).slope hS hN < c :=
    EReal.coe_lt_coe_iff.mp (hm.trans_lt hU)
  refine ⟨U.val, U.property, by omega, hU, ?_⟩
  rw [degree_eq_rank_mul_slope]
  exact mul_le_mul_of_nonneg_left hmean.le (Nat.cast_nonneg _)

/-- Actual restriction slot comparisons and the ambient minimum account
for every omitted ambient slot by one quotient-rank copy of a real lower bound. -/
theorem sum_generalHNOrderedSlope_restrict_add_quotient_rank_mul_le
    (U : Submodule K E) (b : ℝ) (hb : (b : EReal) ≤ V.minimalSlope hS hN) :
    (∑ j, (V.restrictOfMeasurableBase U hS).generalHNOrderedSlope hS hN j) +
      (Module.finrank K (E ⧸ U) : ℝ) * b ≤ ∑ j, V.generalHNOrderedSlope hS hN j := by
  classical
  let e := Fin.castLE U.finrank_le
  have hn : ∀ j, 0 ≤ V.generalHNOrderedSlope hS hN j - b := by
    intro j
    exact sub_nonneg.mpr (EReal.coe_le_coe_iff.mp
      (hb.trans (V.minimalSlope_le_generalHNOrderedSlope hS hN j)))
  have hsum :
      (∑ j, ((V.restrictOfMeasurableBase U hS).generalHNOrderedSlope hS hN j - b)) ≤
        ∑ j : Fin (Module.finrank K U), (V.generalHNOrderedSlope hS hN (e j) - b) := by
    apply Finset.sum_le_sum
    intro j _
    exact sub_le_sub_right (V.generalHNOrderedSlope_restrict_le hS hN U j) b
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.univ.image e)) (fun j _ _ ↦ hn j)
  rw [Finset.sum_image (Fin.castLE_injective U.finrank_le).injOn] at hsub
  have hs := hsum.trans hsub
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  have hr : (Module.finrank K (E ⧸ U) : ℝ) + (Module.finrank K U : ℝ) =
      (Module.finrank K E : ℝ) := by exact_mod_cast U.finrank_quotient_add_finrank
  rw [← hr, add_mul] at hs
  linarith

private theorem degree_sub_majorantDiscrepancy_le_sum_generalHNOrderedSlope_aux (r : ℕ) :
    ∀ {F : Type w} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
      (W : AdelicVectorBundle S F), Module.finrank K F = r →
      (W.degree hS hN : EReal) - W.majorantDiscrepancy hN ≤
        ((∑ j, W.generalHNOrderedSlope hS hN j) : ℝ) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro F _ _ _ W hr
    by_cases hz : Module.finrank K F = 0
    · let : IsEmpty (Fin (Module.finrank K F)) := by rw [hz]; infer_instance
      rw [W.degree_eq_zero_of_finrank_eq_zero hS hN hz,
        W.majorantDiscrepancy_eq_zero_of_finrank_eq_zero hN hz]
      simp
    have hp : 0 < Module.finrank K F := Nat.pos_of_ne_zero hz
    by_cases hD : W.majorantDiscrepancy hN = ⊤
    · rw [hD, EReal.sub_top]
      exact bot_le
    obtain ⟨d, hd⟩ : ∃ d : ℝ, W.majorantDiscrepancy hN = (d : EReal) := by
      lift W.majorantDiscrepancy hN to ℝ using
        ⟨hD, (W.bot_lt_majorantDiscrepancy hN).ne'⟩ with d
      exact ⟨d, rfl⟩
    rw [hd, ← EReal.coe_sub]
    apply EReal.coe_le_coe
    obtain ⟨b, hb⟩ := W.exists_minimalSlope_eq_coe hS hN hp
    apply le_of_forall_pos_le_add
    intro η hη
    let ε := η / (Module.finrank K F : ℝ)
    have hpos : 0 < (Module.finrank K F : ℝ) := Nat.cast_pos.mpr hp
    have hε : 0 < ε := div_pos hη hpos
    have hc : W.minimalSlope hS hN < ((b + ε : ℝ) : EReal) := by
      rw [hb]
      apply EReal.coe_lt_coe
      linarith
    obtain ⟨U, hQ, hU, hmax, hdegQ⟩ :=
      W.exists_quotient_maximalSlope_lt_of_minimalSlope_lt hS hN (b + ε) hc
    have hUr : Module.finrank K U < r := by simpa only [hr] using hU
    have hDU : (W.restrictOfMeasurableBase U hS).majorantDiscrepancy hN ≠ ⊤ :=
      ne_of_lt ((W.majorantDiscrepancy_restrict_le U hS hN).trans_lt
        (lt_top_iff_ne_top.mpr hD))
    obtain ⟨du, hdu⟩ : ∃ du : ℝ,
        (W.restrictOfMeasurableBase U hS).majorantDiscrepancy hN = (du : EReal) := by
      lift (W.restrictOfMeasurableBase U hS).majorantDiscrepancy hN to ℝ using
        ⟨hDU, ((W.restrictOfMeasurableBase U hS).bot_lt_majorantDiscrepancy hN).ne'⟩ with du
      exact ⟨du, rfl⟩
    have hi := ih (Module.finrank K U) hUr (W.restrictOfMeasurableBase U hS) rfl
    rw [hdu, ← EReal.coe_sub] at hi
    have hi' := EReal.coe_le_coe_iff.mp hi
    have hdrop : (W.degree hS hN : EReal) +
        (W.restrictOfMeasurableBase U hS).majorantDiscrepancy hN ≤
      (W.degree hS hN : EReal) +
        (W.restrictOfMeasurableBase U hS).majorantDiscrepancy hN +
          (W.quotientOfMeasurableBase U hS).majorantDiscrepancy hN := by
      simpa only [add_zero] using add_le_add_right
        ((W.quotientOfMeasurableBase U hS).majorantDiscrepancy_nonneg hN)
        ((W.degree hS hN : EReal) +
          (W.restrictOfMeasurableBase U hS).majorantDiscrepancy hN)
    have hs := hdrop.trans (W.degree_add_majorantDiscrepancy_restrict_add_quotient_le U hS hN)
    rw [hd, hdu] at hs
    simp only [← EReal.coe_add, EReal.coe_le_coe_iff] at hs
    have htail := W.sum_generalHNOrderedSlope_restrict_add_quotient_rank_mul_le hS hN U b hb.ge
    have hqle : Module.finrank K (F ⧸ U) ≤ Module.finrank K F := by
      have h := U.finrank_quotient_add_finrank
      omega
    have hqle' : (Module.finrank K (F ⧸ U) : ℝ) ≤ (Module.finrank K F : ℝ) :=
      Nat.cast_le.mpr hqle
    have heq : ε * (Module.finrank K F : ℝ) = η := div_mul_cancel₀ η hpos.ne'
    have herr : (Module.finrank K (F ⧸ U) : ℝ) * ε ≤ η := by
      calc
        _ ≤ (Module.finrank K F : ℝ) * ε := mul_le_mul_of_nonneg_right hqle' hε.le
        _ = η := by rw [mul_comm]; exact heq
    rw [mul_add] at hdegQ
    linarith

/-- Actual degree minus capital discrepancy is at most the sum of actual
general ordered slopes. Infinite capital discrepancy is handled directly
as a negative-infinite left side, before any real lift or subtraction. -/
theorem degree_sub_majorantDiscrepancy_le_sum_generalHNOrderedSlope :
    (V.degree hS hN : EReal) - V.majorantDiscrepancy hN ≤
      ((∑ j, V.generalHNOrderedSlope hS hN j) : ℝ) :=
  degree_sub_majorantDiscrepancy_le_sum_generalHNOrderedSlope_aux hS hN
    (Module.finrank K E) V rfl

/-- Source inequality (4.68) with the actual global capital discrepancy,
including its positive-infinite branch and the empty rank-zero sum. -/
theorem degree_le_sum_generalHNOrderedSlope_add_majorantDiscrepancy :
    (V.degree hS hN : EReal) ≤
      ((∑ j, V.generalHNOrderedSlope hS hN j) : ℝ) + V.majorantDiscrepancy hN := by
  by_cases hD : V.majorantDiscrepancy hN = ⊤
  · rw [hD, EReal.coe_add_top]
    exact le_top
  obtain ⟨d, hd⟩ : ∃ d : ℝ, V.majorantDiscrepancy hN = (d : EReal) := by
    lift V.majorantDiscrepancy hN to ℝ using
      ⟨hD, (V.bot_lt_majorantDiscrepancy hN).ne'⟩ with d
    exact ⟨d, rfl⟩
  have h := V.degree_sub_majorantDiscrepancy_le_sum_generalHNOrderedSlope hS hN
  rw [hd, ← EReal.coe_sub] at h
  rw [hd, ← EReal.coe_add]
  apply EReal.coe_le_coe
  have hr := EReal.coe_le_coe_iff.mp h
  linarith

private theorem degree_sub_determinantDiscrepancy_le_sum_generalHNOrderedSlope_aux (r : ℕ) :
    ∀ {F : Type w} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
      (W : AdelicVectorBundle S F), Module.finrank K F = r → W.IsUltrametric →
      W.degree hS hN - W.determinantDiscrepancy ≤ ∑ j, W.generalHNOrderedSlope hS hN j := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro F _ _ _ W hr hW
    by_cases hz : Module.finrank K F = 0
    · let : IsEmpty (Fin (Module.finrank K F)) := by rw [hz]; infer_instance
      rw [W.degree_eq_zero_of_finrank_eq_zero hS hN hz,
        W.determinantDiscrepancy_eq_zero_of_finrank_eq_zero hz]
      simp
    have hp : 0 < Module.finrank K F := Nat.pos_of_ne_zero hz
    obtain ⟨b, hb⟩ := W.exists_minimalSlope_eq_coe hS hN hp
    apply le_of_forall_pos_le_add
    intro η hη
    let ε := η / (Module.finrank K F : ℝ)
    have hpos : 0 < (Module.finrank K F : ℝ) := Nat.cast_pos.mpr hp
    have hε : 0 < ε := div_pos hη hpos
    have hc : W.minimalSlope hS hN < ((b + ε : ℝ) : EReal) := by
      rw [hb]
      apply EReal.coe_lt_coe
      linarith
    obtain ⟨U, hQ, hU, hmax, hdegQ⟩ :=
      W.exists_quotient_maximalSlope_lt_of_minimalSlope_lt hS hN (b + ε) hc
    have hUr : Module.finrank K U < r := by simpa only [hr] using hU
    have hWU : (W.restrictOfMeasurableBase U hS).IsUltrametric := by
      simpa only [restrictOfMeasurableBase_toNormFamily] using hW.restrict U
    have hi := ih (Module.finrank K U) hUr (W.restrictOfMeasurableBase U hS) rfl hWU
    have hs := W.degree_sub_determinantDiscrepancy_le_restrict_add_quotient U hS hN hW
    have hn := (W.quotientOfMeasurableBase U hS).determinantDiscrepancy_nonneg
    have htail := W.sum_generalHNOrderedSlope_restrict_add_quotient_rank_mul_le hS hN U b hb.ge
    have hqle : Module.finrank K (F ⧸ U) ≤ Module.finrank K F := by
      have h := U.finrank_quotient_add_finrank
      omega
    have hqle' : (Module.finrank K (F ⧸ U) : ℝ) ≤ (Module.finrank K F : ℝ) :=
      Nat.cast_le.mpr hqle
    have heq : ε * (Module.finrank K F : ℝ) = η := div_mul_cancel₀ η hpos.ne'
    have herr : (Module.finrank K (F ⧸ U) : ℝ) * ε ≤ η := by
      calc
        _ ≤ (Module.finrank K F : ℝ) * ε := mul_le_mul_of_nonneg_right hqle' hε.le
        _ = η := by rw [mul_comm]; exact heq
    rw [mul_add] at hdegQ
    linarith

/-- Source inequality (4.69) in corrected form, with the actual
finite-place ultrametric premise and the actual finite determinant discrepancy. -/
theorem degree_sub_determinantDiscrepancy_le_sum_generalHNOrderedSlope
    (hV : V.IsUltrametric) :
    V.degree hS hN - V.determinantDiscrepancy ≤ ∑ j, V.generalHNOrderedSlope hS hN j :=
  degree_sub_determinantDiscrepancy_le_sum_generalHNOrderedSlope_aux hS hN
    (Module.finrank K E) V rfl hV

/-- Actual determinant discrepancy bounds the ordinary degree above
the full general ordered-slope sum. Zero rank has an empty sum. -/
theorem degree_le_sum_generalHNOrderedSlope_add_determinantDiscrepancy
    (hV : V.IsUltrametric) :
    V.degree hS hN ≤ (∑ j, V.generalHNOrderedSlope hS hN j) + V.determinantDiscrepancy := by
  have h := V.degree_sub_determinantDiscrepancy_le_sum_generalHNOrderedSlope hS hN hV
  linarith

/-- Every actual restricted ordered sum is bounded by the ambient sum
of positive parts, by actual slot comparison and nonnegative omitted slots. -/
theorem sum_generalHNOrderedSlope_restrict_le_sum_max (U : Submodule K E) :
    (∑ j, (V.restrictOfMeasurableBase U hS).generalHNOrderedSlope hS hN j) ≤
      ∑ j, max (V.generalHNOrderedSlope hS hN j) 0 := by
  classical
  let e := Fin.castLE U.finrank_le
  have hs :
      (∑ j, (V.restrictOfMeasurableBase U hS).generalHNOrderedSlope hS hN j) ≤
        ∑ j : Fin (Module.finrank K U), max (V.generalHNOrderedSlope hS hN (e j)) 0 := by
    apply Finset.sum_le_sum
    intro j _
    exact (V.generalHNOrderedSlope_restrict_le hS hN U j).trans (le_max_left _ _)
  have ht := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.univ.image e)) (fun j _ _ ↦ le_max_right
      (V.generalHNOrderedSlope hS hN j) 0)
  rw [Finset.sum_image (Fin.castLE_injective U.finrank_le).injOn] at ht
  exact hs.trans ht

/-- Source positive-degree inequality (4.70), by testing every actual
restricted degree in the defining supremum. Infinite capital discrepancy
is allowed, and zero rank has an empty positive-part sum. -/
theorem positiveDegree_le_sum_max_generalHNOrderedSlope_add_majorantDiscrepancy :
    V.positiveDegree hS hN ≤
      ((∑ j, max (V.generalHNOrderedSlope hS hN j) 0) : ℝ) + V.majorantDiscrepancy hN := by
  apply V.positiveDegree_le hS hN
  intro U
  have hd := degree_le_sum_generalHNOrderedSlope_add_majorantDiscrepancy
    (V.restrictOfMeasurableBase U hS) hS hN
  exact hd.trans
    (add_le_add (EReal.coe_le_coe_iff.mpr
      (V.sum_generalHNOrderedSlope_restrict_le_sum_max hS hN U))
      (V.majorantDiscrepancy_restrict_le U hS hN))

/-- Source positive-degree inequality (4.71) with the true finite-place
ultrametric hypothesis, inherited by every actual restricted norm family. -/
theorem positiveDegree_le_sum_max_generalHNOrderedSlope_add_determinantDiscrepancy
    (hV : V.IsUltrametric) :
    V.positiveDegree hS hN ≤
      (((∑ j, max (V.generalHNOrderedSlope hS hN j) 0) + V.determinantDiscrepancy) : ℝ) := by
  apply V.positiveDegree_le hS hN
  intro U
  apply EReal.coe_le_coe
  have hVU : (V.restrictOfMeasurableBase U hS).IsUltrametric := by
    simpa only [restrictOfMeasurableBase_toNormFamily] using hV.restrict U
  have hd := degree_le_sum_generalHNOrderedSlope_add_determinantDiscrepancy
    (V.restrictOfMeasurableBase U hS) hS hN hVU
  have hs := V.sum_generalHNOrderedSlope_restrict_le_sum_max hS hN U
  have hδ := V.determinantDiscrepancy_restrict_le U hS hN hV
  linarith

end

end ArakelovGeometry.AdelicVectorBundle

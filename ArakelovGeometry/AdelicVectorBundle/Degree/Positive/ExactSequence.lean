/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic
public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.ExactSequence
import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Dual
import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Majorant
import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.Determinant.ExactSequence.Dual
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Restriction
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Positive degree in actual restriction-quotient sequences

Every actual ambient subspace is tested. Its quotient-image contraction
compares the quotient degree with ambient quotient positive degree. The genuine
capital discrepancy may be infinite; determinant discrepancy is finite under
the source ultrametric hypothesis. No supremum attainment is assumed.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual quotient of a restriction contracts into its ambient quotient
image, so its degree is bounded by ambient quotient positive degree. -/
theorem degree_quotient_restrict_le_positiveDegree_quotient (V : AdelicVectorBundle S)
    (U W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (((V.restrictOfNormMeasurability U).quotientOfNormMeasurability
      (W.mkQ.comp U.subtype).ker).degree : EReal) ≤
      (V.quotientOfNormMeasurability W).positiveDegree := by
  let g : U →ₗ[K] V ⧸ W := W.mkQ.comp U.subtype
  have hd := degree_le_of_completed_contraction
    ((V.restrictOfNormMeasurability U).quotientOfNormMeasurability g.ker)
    ((V.quotientOfNormMeasurability W).restrictOfNormMeasurability g.range)
    g.quotKerEquivRange
    (V.toNormFamily.quotient_restrict_range_norm_le U W)
  exact (EReal.coe_le_coe_iff.mpr hd).trans
    ((V.quotientOfNormMeasurability W).degree_restrict_le_positiveDegree g.range)

/-- The intersection degree is a genuine restricted degree inside `W`. -/
theorem degree_restrict_inf_le_positiveDegree_restrict (V : AdelicVectorBundle S)
    (U W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    ((V.restrictOfNormMeasurability (U ⊓ W)).degree : EReal) ≤
      (V.restrictOfNormMeasurability W).positiveDegree := by
  have h := (V.restrictOfNormMeasurability W).degree_restrict_le_positiveDegree
    ((U ⊓ W).comap W.subtype)
  rw [V.degree_restrict_restrict (U ⊓ W) W inf_le_right] at h
  exact h

omit [S.IsProper] in
/-- Actual determinant discrepancy decreases under restriction when the
original norms are ultrametric outside infinity. -/
theorem determinantDiscrepancy_restrict_le (V : AdelicVectorBundle S)
    (U : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametricAtFinitePlaces] :
    (V.restrictOfNormMeasurability U).determinantDiscrepancy ≤ V.determinantDiscrepancy := by
  apply integral_mono
    ((V.restrictOfNormMeasurability U).integrable_log_determinantDiscrepancy)
    (V.integrable_log_determinantDiscrepancy)
  intro ω
  apply Real.log_le_log ((V.toNormFamily.restrict U).determinantDiscrepancy_pos ω)
  apply V.toNormFamily.determinantDiscrepancy_restrict_le U ω
  by_cases hω : ω ∈ S.Ωinf
  · exact Or.inl (hN ω hω)
  · exact Or.inr (hV ω (by simpa only [AdelicStructure.Ωinf, AdelicStructure.Ωfin,
      Set.mem_ofPred_eq, not_not] using hω))

/-- The two-step capital bound controls each actual ambient restricted degree.
The two real end degrees make the extended subtraction-to-addition step valid
even if one of the genuine capital discrepancies is positive infinity. -/
theorem degree_restrict_le_positiveDegree_restrict_add_quotient_add_majorantDiscrepancy
    (V : AdelicVectorBundle S) (U W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    ((V.restrictOfNormMeasurability U).degree : EReal) ≤
      (V.restrictOfNormMeasurability W).positiveDegree +
        (V.quotientOfNormMeasurability W).positiveDegree +
          V.majorantDiscrepancy := by
  let P := V.restrictOfNormMeasurability U
  let I := (W.mkQ.comp U.subtype).ker
  let R := P.restrictOfNormMeasurability I
  let Q := P.quotientOfNormMeasurability I
  have hI : (U ⊓ W).comap U.subtype = I := by
    simp only [I, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_inf]
    simp
  have hR : (R.degree : EReal) ≤
      (V.restrictOfNormMeasurability W).positiveDegree := by
    have hd := V.degree_restrict_restrict (U ⊓ W) U inf_le_left
    rw [hI] at hd
    change R.degree = _ at hd
    rw [hd]
    exact V.degree_restrict_inf_le_positiveDegree_restrict U W
  have hQ : (Q.degree : EReal) ≤
      (V.quotientOfNormMeasurability W).positiveDegree :=
    V.degree_quotient_restrict_le_positiveDegree_quotient U W
  have hRs : (R.degree : EReal) - R.majorantDiscrepancy ≤ R.degree := by
    simpa only [sub_zero] using EReal.sub_le_sub (le_refl (R.degree : EReal))
      (R.majorantDiscrepancy_nonneg)
  have hQs : (Q.degree : EReal) - Q.majorantDiscrepancy ≤ Q.degree := by
    simpa only [sub_zero] using EReal.sub_le_sub (le_refl (Q.degree : EReal))
      (Q.majorantDiscrepancy_nonneg)
  have hb := (P.degree_sub_majorantDiscrepancy_le_restrict_add_quotient I).trans
    (add_le_add hRs hQs)
  rw [← EReal.coe_add] at hb
  have hc := (EReal.sub_le_iff_le_add
    (Or.inr (EReal.coe_ne_top (R.degree + Q.degree)))
    (Or.inr (EReal.coe_ne_bot (R.degree + Q.degree)))).mp hb
  rw [EReal.coe_add] at hc
  exact hc.trans (add_le_add (add_le_add hR hQ) (V.majorantDiscrepancy_restrict_le U))

/-- Source (4.36) for the actual restriction-quotient sequence, with all
ambient subspaces and infinite capital discrepancy retained. -/
theorem positiveDegree_le_restrict_add_quotient_add_majorantDiscrepancy
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    V.positiveDegree ≤ (V.restrictOfNormMeasurability W).positiveDegree +
      (V.quotientOfNormMeasurability W).positiveDegree + V.majorantDiscrepancy := by
  apply V.positiveDegree_le
  intro U
  exact V.degree_restrict_le_positiveDegree_restrict_add_quotient_add_majorantDiscrepancy
    U W

/-- The finite determinant-discrepancy variant controls each actual
restricted degree under the source ultrametric-outside-infinity hypothesis. -/
theorem degree_restrict_le_positiveDegree_restrict_add_quotient_add_determinantDiscrepancy
    (V : AdelicVectorBundle S) (U W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametricAtFinitePlaces] :
    ((V.restrictOfNormMeasurability U).degree : EReal) ≤
      (V.restrictOfNormMeasurability W).positiveDegree +
        (V.quotientOfNormMeasurability W).positiveDegree +
          (V.determinantDiscrepancy : EReal) := by
  let P := V.restrictOfNormMeasurability U
  let I := (W.mkQ.comp U.subtype).ker
  let R := P.restrictOfNormMeasurability I
  let Q := P.quotientOfNormMeasurability I
  have hI : (U ⊓ W).comap U.subtype = I := by
    simp only [I, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_inf]
    simp
  have hR : (R.degree : EReal) ≤
      (V.restrictOfNormMeasurability W).positiveDegree := by
    have hd := V.degree_restrict_restrict (U ⊓ W) U inf_le_left
    rw [hI] at hd
    change R.degree = _ at hd
    rw [hd]
    exact V.degree_restrict_inf_le_positiveDegree_restrict U W
  have hQ : (Q.degree : EReal) ≤
      (V.quotientOfNormMeasurability W).positiveDegree :=
    V.degree_quotient_restrict_le_positiveDegree_quotient U W
  have hs := P.degree_sub_determinantDiscrepancy_le_restrict_add_quotient I
    (hV := (hV.restrict U))
  have hP := V.determinantDiscrepancy_restrict_le U
  have hd : P.degree ≤ R.degree + Q.degree +
      V.determinantDiscrepancy := by
    have hRd := R.determinantDiscrepancy_nonneg
    have hQd := Q.determinantDiscrepancy_nonneg
    linarith
  have hb := EReal.coe_le_coe_iff.mpr hd
  rw [EReal.coe_add, EReal.coe_add] at hb
  exact hb.trans (add_le_add (add_le_add hR hQ) le_rfl)

/-- Source (4.37), with actual determinant discrepancy and no attained
positive-degree supremum as a premise. -/
theorem positiveDegree_le_restrict_add_quotient_add_determinantDiscrepancy
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametricAtFinitePlaces] :
    V.positiveDegree ≤ (V.restrictOfNormMeasurability W).positiveDegree +
      (V.quotientOfNormMeasurability W).positiveDegree +
        (V.determinantDiscrepancy : EReal) := by
  apply V.positiveDegree_le
  intro U
  exact V.degree_restrict_le_positiveDegree_restrict_add_quotient_add_determinantDiscrepancy
    U W

/-- Hermitian vanishing of the actual discrepancy removes the exact-sequence
error term in the positive-degree bound. -/
theorem positiveDegree_le_restrict_add_quotient_of_isHermitian
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    V.positiveDegree ≤ (V.restrictOfNormMeasurability W).positiveDegree +
      (V.quotientOfNormMeasurability W).positiveDegree := by
  have h := V.positiveDegree_le_restrict_add_quotient_add_determinantDiscrepancy W (hV := hV.1)
  simpa only [V.determinantDiscrepancy_eq_zero_of_isHermitian,
    EReal.coe_zero, add_zero] using h

end

end ArakelovGeometry.AdelicVectorBundle

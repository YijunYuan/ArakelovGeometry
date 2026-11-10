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

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual quotient of a restriction contracts into its ambient quotient
image, so its degree is bounded by ambient quotient positive degree. -/
theorem degree_quotient_restrict_le_positiveDegree_quotient (V : AdelicVectorBundle S E)
    (U W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (((V.restrictOfMeasurableBase U hS).quotientOfMeasurableBase
      (W.mkQ.comp U.subtype).ker hS).degree hS hN : EReal) ≤
      (V.quotientOfMeasurableBase W hS).positiveDegree hS hN := by
  let g : U →ₗ[K] E ⧸ W := W.mkQ.comp U.subtype
  have hd := degree_le_of_completed_contraction
    ((V.restrictOfMeasurableBase U hS).quotientOfMeasurableBase g.ker hS)
    ((V.quotientOfMeasurableBase W hS).restrictOfMeasurableBase g.range hS)
    g.quotKerEquivRange hS hN
    (V.toNormFamily.quotient_restrict_range_norm_le U W)
  exact (EReal.coe_le_coe_iff.mpr hd).trans
    ((V.quotientOfMeasurableBase W hS).degree_restrict_le_positiveDegree hS hN g.range)

/-- The intersection degree is a genuine restricted degree inside `W`. -/
theorem degree_restrict_inf_le_positiveDegree_restrict (V : AdelicVectorBundle S E)
    (U W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.restrictOfMeasurableBase (U ⊓ W) hS).degree hS hN : EReal) ≤
      (V.restrictOfMeasurableBase W hS).positiveDegree hS hN := by
  have h := (V.restrictOfMeasurableBase W hS).degree_restrict_le_positiveDegree
    hS hN ((U ⊓ W).comap W.subtype)
  rw [V.degree_restrict_restrict (U ⊓ W) W inf_le_right hS hN] at h
  exact h

omit [S.IsProper] in
/-- Actual determinant discrepancy decreases under restriction when the
original norms are ultrametric outside infinity. -/
theorem determinantDiscrepancy_restrict_le (V : AdelicVectorBundle S E)
    (U : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsUltrametric) :
    (V.restrictOfMeasurableBase U hS).determinantDiscrepancy ≤ V.determinantDiscrepancy := by
  apply integral_mono
    ((V.restrictOfMeasurableBase U hS).integrable_log_determinantDiscrepancy hS hN)
    (V.integrable_log_determinantDiscrepancy hS hN)
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
    (V : AdelicVectorBundle S E) (U W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.restrictOfMeasurableBase U hS).degree hS hN : EReal) ≤
      (V.restrictOfMeasurableBase W hS).positiveDegree hS hN +
        (V.quotientOfMeasurableBase W hS).positiveDegree hS hN +
          V.majorantDiscrepancy hN := by
  let P := V.restrictOfMeasurableBase U hS
  let I := (W.mkQ.comp U.subtype).ker
  let R := P.restrictOfMeasurableBase I hS
  let Q := P.quotientOfMeasurableBase I hS
  have hI : (U ⊓ W).comap U.subtype = I := by
    simp only [I, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_inf]
    simp
  have hR : (R.degree hS hN : EReal) ≤
      (V.restrictOfMeasurableBase W hS).positiveDegree hS hN := by
    have hd := V.degree_restrict_restrict (U ⊓ W) U inf_le_left hS hN
    rw [hI] at hd
    change R.degree hS hN = _ at hd
    rw [hd]
    exact V.degree_restrict_inf_le_positiveDegree_restrict U W hS hN
  have hQ : (Q.degree hS hN : EReal) ≤
      (V.quotientOfMeasurableBase W hS).positiveDegree hS hN :=
    V.degree_quotient_restrict_le_positiveDegree_quotient U W hS hN
  have hRs : (R.degree hS hN : EReal) - R.majorantDiscrepancy hN ≤ R.degree hS hN := by
    simpa only [sub_zero] using EReal.sub_le_sub (le_refl (R.degree hS hN : EReal))
      (R.majorantDiscrepancy_nonneg hN)
  have hQs : (Q.degree hS hN : EReal) - Q.majorantDiscrepancy hN ≤ Q.degree hS hN := by
    simpa only [sub_zero] using EReal.sub_le_sub (le_refl (Q.degree hS hN : EReal))
      (Q.majorantDiscrepancy_nonneg hN)
  have hb := (P.degree_sub_majorantDiscrepancy_le_restrict_add_quotient I hS hN).trans
    (add_le_add hRs hQs)
  rw [← EReal.coe_add] at hb
  have hc := (EReal.sub_le_iff_le_add
    (Or.inr (EReal.coe_ne_top (R.degree hS hN + Q.degree hS hN)))
    (Or.inr (EReal.coe_ne_bot (R.degree hS hN + Q.degree hS hN)))).mp hb
  rw [EReal.coe_add] at hc
  exact hc.trans (add_le_add (add_le_add hR hQ) (V.majorantDiscrepancy_restrict_le U hS hN))

/-- Source (4.36) for the actual restriction-quotient sequence, with all
ambient subspaces and infinite capital discrepancy retained. -/
theorem positiveDegree_le_restrict_add_quotient_add_majorantDiscrepancy
    (V : AdelicVectorBundle S E) (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.positiveDegree hS hN ≤ (V.restrictOfMeasurableBase W hS).positiveDegree hS hN +
      (V.quotientOfMeasurableBase W hS).positiveDegree hS hN + V.majorantDiscrepancy hN := by
  apply V.positiveDegree_le hS hN
  intro U
  exact V.degree_restrict_le_positiveDegree_restrict_add_quotient_add_majorantDiscrepancy
    U W hS hN

/-- The finite determinant-discrepancy variant controls each actual
restricted degree under the source ultrametric-outside-infinity hypothesis. -/
theorem degree_restrict_le_positiveDegree_restrict_add_quotient_add_determinantDiscrepancy
    (V : AdelicVectorBundle S E) (U W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsUltrametric) :
    ((V.restrictOfMeasurableBase U hS).degree hS hN : EReal) ≤
      (V.restrictOfMeasurableBase W hS).positiveDegree hS hN +
        (V.quotientOfMeasurableBase W hS).positiveDegree hS hN +
          (V.determinantDiscrepancy : EReal) := by
  let P := V.restrictOfMeasurableBase U hS
  let I := (W.mkQ.comp U.subtype).ker
  let R := P.restrictOfMeasurableBase I hS
  let Q := P.quotientOfMeasurableBase I hS
  have hI : (U ⊓ W).comap U.subtype = I := by
    simp only [I, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_inf]
    simp
  have hR : (R.degree hS hN : EReal) ≤
      (V.restrictOfMeasurableBase W hS).positiveDegree hS hN := by
    have hd := V.degree_restrict_restrict (U ⊓ W) U inf_le_left hS hN
    rw [hI] at hd
    change R.degree hS hN = _ at hd
    rw [hd]
    exact V.degree_restrict_inf_le_positiveDegree_restrict U W hS hN
  have hQ : (Q.degree hS hN : EReal) ≤
      (V.quotientOfMeasurableBase W hS).positiveDegree hS hN :=
    V.degree_quotient_restrict_le_positiveDegree_quotient U W hS hN
  have hs := P.degree_sub_determinantDiscrepancy_le_restrict_add_quotient I hS hN
    (hV.restrict U)
  have hP := V.determinantDiscrepancy_restrict_le U hS hN hV
  have hd : P.degree hS hN ≤ R.degree hS hN + Q.degree hS hN +
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
    (V : AdelicVectorBundle S E) (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsUltrametric) :
    V.positiveDegree hS hN ≤ (V.restrictOfMeasurableBase W hS).positiveDegree hS hN +
      (V.quotientOfMeasurableBase W hS).positiveDegree hS hN +
        (V.determinantDiscrepancy : EReal) := by
  apply V.positiveDegree_le hS hN
  intro U
  exact V.degree_restrict_le_positiveDegree_restrict_add_quotient_add_determinantDiscrepancy
    U W hS hN hV

/-- Hermitian vanishing of the actual discrepancy removes the exact-sequence
error term in the positive-degree bound. -/
theorem positiveDegree_le_restrict_add_quotient_of_isHermitian
    (V : AdelicVectorBundle S E) (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    V.positiveDegree hS hN ≤ (V.restrictOfMeasurableBase W hS).positiveDegree hS hN +
      (V.quotientOfMeasurableBase W hS).positiveDegree hS hN := by
  have h := V.positiveDegree_le_restrict_add_quotient_add_determinantDiscrepancy W hS hN hV.1
  simpa only [V.determinantDiscrepancy_eq_zero_of_isHermitian hN hV,
    EReal.coe_zero, add_zero] using h

end

end ArakelovGeometry.AdelicVectorBundle

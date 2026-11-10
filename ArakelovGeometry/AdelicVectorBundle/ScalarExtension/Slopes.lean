/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Bundle
import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.Degree
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual degrees and slopes increase on algebraic closure

The original subspace extends to a genuine native subspace. Its entire
completed norm is bounded by the extension of the original restricted norm.
Determinant contraction and degree preservation then compare actual degrees;
taking the actual suprema compares positive degree and maximal slope.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

universe u v w wL

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]

/-- The original restricted degree is at most the degree of the actual native
restriction after ordinary extension, without original ultrametricity. -/
theorem degree_le_restrict_scalarExtension
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule K E) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.restrictOfMeasurableBase A (Or.inr hcount)).degree (Or.inr hcount) hN ≤
    ((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase
      (A.baseChange L) (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))).degree
      (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let hL : DiscreteMeasurableSpace (S.algebraicExtension L).Ω ∨
      (S.algebraicExtension L).HasCommonCountableDenseSubfield :=
    Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let W := (V.restrictOfMeasurableBase A (Or.inr hcount)).scalarExtension (L := L) hcount hN
  let R := (V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase (A.baseChange L) hL
  have he : W.degree hL hLN ≤ R.degree hL hLN :=
    W.degree_le_of_completed_contraction R (Submodule.toBaseChange.toLinearEquiv L A)
      hL hLN (fun x z => V.toNormFamily.scalarExtension_restrict_norm_le A x z)
  exact ((V.restrictOfMeasurableBase A (Or.inr hcount)).degree_scalarExtension_of_isAlgClosed
    (L := L) hcount hN).symm.le.trans he

/-- Mean slopes of actual native restrictions increase, including rank zero. -/
theorem slope_le_restrict_scalarExtension
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule K E) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.restrictOfMeasurableBase A (Or.inr hcount)).slope (Or.inr hcount) hN ≤
    ((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase
      (A.baseChange L) (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))).slope
      (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  unfold slope
  have hr := V.rank_restrict_scalarExtension (L := L) hcount hN A
  change Module.finrank L (A.baseChange L) = Module.finrank K A at hr
  rw [hr]
  exact div_le_div_of_nonneg_right (V.degree_le_restrict_scalarExtension hcount hN A)
    (Nat.cast_nonneg _)

/-- Every original subspace gives an actual extended subspace, so positive
 degree increases under ordinary extension to an algebraically closed target. -/
theorem positiveDegree_le_scalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    V.positiveDegree (Or.inr hcount) hN ≤
    (V.scalarExtension (L := L) hcount hN).positiveDegree
      (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  apply V.positiveDegree_le (Or.inr hcount) hN
  intro A
  exact (EReal.coe_le_coe_iff.mpr (V.degree_le_restrict_scalarExtension hcount hN A)).trans
    ((V.scalarExtension (L := L) hcount hN).degree_restrict_le_positiveDegree
      (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) (A.baseChange L))

/-- The actual maximal slope increases on algebraic closure, with the empty
positive-rank supremum convention in rank zero. -/
theorem maximalSlope_le_scalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    V.maximalSlope (Or.inr hcount) hN ≤
    (V.scalarExtension (L := L) hcount hN).maximalSlope
      (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  apply V.maximalSlope_le (Or.inr hcount) hN
  intro A hA
  have hr : 0 < Module.finrank L (A.baseChange L) := by
    have he := V.rank_restrict_scalarExtension (L := L) hcount hN A
    change Module.finrank L (A.baseChange L) = Module.finrank K A at he
    simpa only [he] using hA
  exact (EReal.coe_le_coe_iff.mpr (V.slope_le_restrict_scalarExtension hcount hN A)).trans
    ((V.scalarExtension (L := L) hcount hN).slope_restrict_le_maximalSlope
      (A.baseChange L) hr (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN))

end ArakelovGeometry.AdelicVectorBundle

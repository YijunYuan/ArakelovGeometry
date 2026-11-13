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

universe u w wL

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]

/-- The original restricted degree is at most the degree of the actual native
restriction after ordinary extension, without original ultrametricity. -/
theorem degree_le_restrict_scalarExtension
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule K V) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.restrictOfNormMeasurability A).degree ≤
    ((V.scalarExtension (L := L)).restrictOfNormMeasurability
      (A.baseChange L) (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed
          (L := L)))⟩)).degree
      (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let hL : DiscreteMeasurableSpace (S.algebraicExtension L).Ω ∨
      (S.algebraicExtension L).HasCommonCountableDenseSubfield :=
    Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let W := (V.restrictOfNormMeasurability A).scalarExtension (L := L)
  let R := (V.scalarExtension (L := L)).restrictOfNormMeasurability (A.baseChange L) (hS := ⟨hL⟩)
  have he : W.degree (hS := ⟨hL⟩) (hN := ⟨hLN⟩) ≤ R.degree (hS := ⟨hL⟩) (hN := ⟨hLN⟩) :=
    W.degree_le_of_completed_contraction R (Submodule.toBaseChange.toLinearEquiv L A)
      (hS := ⟨hL⟩) (hN := ⟨hLN⟩) (fun x z => V.toNormFamily.scalarExtension_restrict_norm_le A x z)
  exact ((V.restrictOfNormMeasurability A).degree_scalarExtension_of_isAlgClosed
    (L := L)).symm.le.trans he

/-- Mean slopes of actual native restrictions increase, including rank zero. -/
theorem slope_le_restrict_scalarExtension
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule K V) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.restrictOfNormMeasurability A).slope ≤
    ((V.scalarExtension (L := L)).restrictOfNormMeasurability
      (A.baseChange L) (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)).slope
      (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  unfold slope
  have hr := V.rank_restrict_scalarExtension (L := L) A
  change Module.finrank L (A.baseChange L) = Module.finrank K A at hr
  rw [hr]
  exact div_le_div_of_nonneg_right (V.degree_le_restrict_scalarExtension A)
    (Nat.cast_nonneg _)

/-- Every original subspace gives an actual extended subspace, so positive
 degree increases under ordinary extension to an algebraically closed target. -/
theorem positiveDegree_le_scalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    V.positiveDegree ≤
    (V.scalarExtension (L := L)).positiveDegree
      (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  apply V.positiveDegree_le
  intro A
  exact (EReal.coe_le_coe_iff.mpr (V.degree_le_restrict_scalarExtension A)).trans
    ((V.scalarExtension (L := L)).degree_restrict_le_positiveDegree
      (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) (A.baseChange L))

/-- The actual maximal slope increases on algebraic closure, with the empty
positive-rank supremum convention in rank zero. -/
theorem maximalSlope_le_scalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    V.maximalSlope ≤
    (V.scalarExtension (L := L)).maximalSlope
      (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  apply V.maximalSlope_le
  intro A hA
  have hr : 0 < Module.finrank L (A.baseChange L) := by
    have he := V.rank_restrict_scalarExtension (L := L) A
    change Module.finrank L (A.baseChange L) = Module.finrank K A at he
    simpa only [he] using hA
  exact (EReal.coe_le_coe_iff.mpr (V.slope_le_restrict_scalarExtension A)).trans
    ((V.scalarExtension (L := L)).slope_restrict_le_maximalSlope
      (A.baseChange L) hr (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩))

end ArakelovGeometry.AdelicVectorBundle

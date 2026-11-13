/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.PositiveAtoms.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Contraction
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual geometric ordinary-to-absolute comparisons

Genuine completed tensor-inclusion contractions compare every original
restricted degree with its actual native closure-image degree. Taking the
actual subspace suprema gives the geometric inequalities of source4.3.67,
without countability of the original place set or target regularity.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [MeasurableSingletonClass S.Ω]

/-- The actual tensor inclusion contracts completed norms and compares the
produced actual determinant degrees, with no extension-place regularity. -/
theorem degree_restrict_le_nativeAlgebraicRestrictionDegreeOfPositiveAtoms
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveAtoms] [hgeo : S.HasOnlyFinitePlaces]
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule K V) :
    (V.restrictOfMeasurableBase A).degree ≤
      V.toNormFamily.nativeAlgebraicRestrictionDegreeOfPositiveAtoms
        (A.baseChange L) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let B := V.restrictOfMeasurableBase A
  let W := B.toNormFamily.algebraicScalarBundleOfPositiveAtoms (L := L)
  let R := V.toNormFamily.nativeAlgebraicRestrictionOfPositiveAtoms
    (A.baseChange L)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let hdetB := B.isMeasurable.determinant_of_discrete_or_countable
  let hdetR :=
    V.isDominated.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      V.toNormFamily (A.baseChange L)
  let : W.toNormFamily.determinant.IsMeasurable := hdetB.determinant_scalarExtension
  let : R.toNormFamily.determinant.IsMeasurable := hdetR
  have he : W.degreeOfMeasurableDeterminant (hdet := hdetB.determinant_scalarExtension)
      (hN := ⟨hLN⟩) ≤
      R.degreeOfMeasurableDeterminant (hdet := hdetR) (hN := ⟨hLN⟩) :=
    W.degreeOfMeasurableDeterminant_le_of_completed_contraction R
      (Submodule.toBaseChange.toLinearEquiv L A) (hN := ⟨hLN⟩)
      (fun x z => V.toNormFamily.scalarExtension_restrict_norm_le A x z)
  change B.degreeOfMeasurableDeterminant (hdet := hdetB) ≤
    R.degreeOfMeasurableDeterminant (hdet := hdetR) (hN := ⟨hLN⟩)
  exact (B.degreeOfMeasurableDeterminant_algebraicScalarBundleOfPositiveAtoms
    (L := L) (hdet := hdetB)).symm.le.trans he

/-- The actual original and native mean degrees compare through unchanged rank. -/
theorem slope_restrict_le_nativeMeanOfPositiveAtoms
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveAtoms] [hgeo : S.HasOnlyFinitePlaces]
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule K V) :
    (V.restrictOfMeasurableBase A).slope ≤
      V.toNormFamily.nativeAlgebraicRestrictionDegreeOfPositiveAtoms
        (A.baseChange L) /
          (Module.finrank L (A.baseChange L) : ℝ) := by
  have hr : Module.finrank L (A.baseChange L) = Module.finrank K A :=
    (Submodule.toBaseChange.toLinearEquiv L A).finrank_eq.symm.trans Module.finrank_baseChange
  change _ / (Module.finrank K A : ℝ) ≤ _ / _
  rw [hr]
  exact div_le_div_of_nonneg_right
    (V.degree_restrict_le_nativeAlgebraicRestrictionDegreeOfPositiveAtoms A)
    (Nat.cast_nonneg _)

/-- All original restricted degrees feed the actual geometric absolute supremum. -/
theorem positiveDegree_le_absolutePositiveDegreeOfPositiveAtoms
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveAtoms] [hgeo : S.HasOnlyFinitePlaces]
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    V.positiveDegree ≤
      V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms := by
  apply V.positiveDegree_le
  intro A
  exact (EReal.coe_le_coe_iff.mpr
    (V.degree_restrict_le_nativeAlgebraicRestrictionDegreeOfPositiveAtoms
      (L := AlgebraicClosure K) A)).trans
    (V.toNormFamily.nativeRestrictionDegree_le_absolutePositiveDegreeOfPositiveAtoms
      (A.baseChange (AlgebraicClosure K)))

/-- Positive-rank original subspaces supply actual positive-rank native mean terms. -/
theorem maximalSlope_le_absoluteMaximalSlopeOfPositiveAtoms
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveAtoms] [hgeo : S.HasOnlyFinitePlaces]
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    V.maximalSlope ≤
      V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms := by
  apply V.maximalSlope_le
  intro A hA
  have hr : Module.finrank (AlgebraicClosure K) (A.baseChange (AlgebraicClosure K)) =
      Module.finrank K A :=
    (Submodule.toBaseChange.toLinearEquiv (AlgebraicClosure K) A).finrank_eq.symm.trans
      Module.finrank_baseChange
  exact (EReal.coe_le_coe_iff.mpr
    (V.slope_restrict_le_nativeMeanOfPositiveAtoms
      (L := AlgebraicClosure K) A)).trans
    (V.toNormFamily.nativeMean_le_absoluteMaximalSlopeOfPositiveAtoms
      (A.baseChange (AlgebraicClosure K)) (hr.symm ▸ hA))

/-- Every actual original restricted degree is bounded by the geometric absolute degree. -/
theorem degree_restrict_le_absolutePositiveDegreeOfPositiveAtoms
    (V : AdelicVectorBundle S)
    [hpos : S.HasPositiveAtoms] [hgeo : S.HasOnlyFinitePlaces]
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule K V) :
    ((V.restrictOfMeasurableBase A).degree : EReal) ≤
      V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms :=
  (V.degree_restrict_le_positiveDegree A).trans
    (V.positiveDegree_le_absolutePositiveDegreeOfPositiveAtoms)

end ArakelovGeometry.AdelicVectorBundle

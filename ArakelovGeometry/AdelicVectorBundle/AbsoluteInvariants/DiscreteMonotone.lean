/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.Discrete

import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Contraction
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.DegreeDeterminant
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Native.Degree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Original invariants bounded by actual countable discrete absolute invariants

Every original subspace gives its actual tensor extension. The genuine completed
contraction compares the produced measurable determinant degrees; the suprema
then compare the original and absolute positive degrees and maximal slopes.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u w wL
variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- The genuine tensor inclusion contraction bounds every original restricted
degree by the actual native target determinant degree, without target regularity. -/
theorem degree_restrict_le_nativeRestrictionDegreeOfCountableDiscreteBase
    {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule K V) :
    (V.restrictOfNormMeasurability A).degree ≤
      V.nativeRestrictionDegreeOfCountableDiscreteBase (A.baseChange L) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let B := V.restrictOfNormMeasurability A
  let W := B.scalarExtensionOfCountableDiscreteBase (L := L)
  let R := V.scalarExtensionRestrictionOfCountableDiscreteBase (A.baseChange L)
  let : R.toNormFamily.determinant.IsMeasurable :=
    V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
      (A.baseChange L)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  have he : W.degreeOfMeasurableDeterminant
      (hdet := (B.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable)) (hN := ⟨hLN⟩) ≤
      R.degreeOfMeasurableDeterminant
        (hdet :=
          (V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
          (A.baseChange L))) (hN := ⟨hLN⟩) :=
    W.degreeOfMeasurableDeterminant_le_of_completed_contraction R
      (hdetV := B.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable (L := L))
      (Submodule.toBaseChange.toLinearEquiv L A) (hN := ⟨hLN⟩)
      (fun x z ↦ V.toNormFamily.scalarExtension_restrict_norm_le A x z)
  exact (B.degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase
    (L := L)).symm.le.trans he

/-- The actual original and native mean degrees compare using their unchanged
rank. The real rank-zero division convention is retained. -/
theorem slope_restrict_le_nativeMeanOfCountableDiscreteBase
    {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule K V) :
    (V.restrictOfNormMeasurability A).slope ≤
      V.nativeRestrictionDegreeOfCountableDiscreteBase (A.baseChange L) /
        (Module.finrank L (A.baseChange L) : ℝ) := by
  have hr : Module.finrank L (A.baseChange L) = Module.finrank K A :=
    (Submodule.toBaseChange.toLinearEquiv L A).finrank_eq.symm.trans Module.finrank_baseChange
  change _ / (Module.finrank K A : ℝ) ≤ _ / _
  rw [hr]
  exact div_le_div_of_nonneg_right
    (V.degree_restrict_le_nativeRestrictionDegreeOfCountableDiscreteBase A)
    (Nat.cast_nonneg _)

/-- Taking ALL original subspaces and their actual closure images compares
positive degree with the genuine absolute supremum. -/
theorem positiveDegree_le_absolutePositiveDegreeOfCountableDiscreteBase
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    V.positiveDegree ≤
      V.absolutePositiveDegreeOfCountableDiscreteBase := by
  apply V.positiveDegree_le
  intro A
  exact (EReal.coe_le_coe_iff.mpr
    (V.degree_restrict_le_nativeRestrictionDegreeOfCountableDiscreteBase
      (L := AlgebraicClosure K) A)).trans
    (V.nativeRestrictionDegree_le_absolutePositiveDegreeOfCountableDiscreteBase
      (A.baseChange (AlgebraicClosure K)))

/-- Positive-rank original subspaces extend with unchanged positive rank, so
their actual mean degrees bound the original maximal-slope supremum. -/
theorem maximalSlope_le_absoluteMaximalSlopeOfCountableDiscreteBase
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    V.maximalSlope ≤
      V.absoluteMaximalSlopeOfCountableDiscreteBase := by
  apply V.maximalSlope_le
  intro A hA
  have hr : Module.finrank (AlgebraicClosure K) (A.baseChange (AlgebraicClosure K)) =
      Module.finrank K A :=
    (Submodule.toBaseChange.toLinearEquiv (AlgebraicClosure K) A).finrank_eq.symm.trans
      Module.finrank_baseChange
  exact (EReal.coe_le_coe_iff.mpr
    (V.slope_restrict_le_nativeMeanOfCountableDiscreteBase
      (L := AlgebraicClosure K) A)).trans
    (V.nativeMean_le_absoluteMaximalSlopeOfCountableDiscreteBase
      (A.baseChange (AlgebraicClosure K)) (hr.symm ▸ hA))

/-- Every actual original restricted degree is bounded by the genuine
absolute positive degree; no caller-supplied native degree bound is used. -/
theorem degree_restrict_le_absolutePositiveDegreeOfCountableDiscreteBase
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule K V) :
    ((V.restrictOfNormMeasurability A).degree
      : EReal) ≤
      V.absolutePositiveDegreeOfCountableDiscreteBase :=
  (V.degree_restrict_le_positiveDegree A).trans
    (V.positiveDegree_le_absolutePositiveDegreeOfCountableDiscreteBase)

end ArakelovGeometry.AdelicVectorBundle

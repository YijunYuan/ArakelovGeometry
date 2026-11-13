/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.Discrete
public import ArakelovGeometry.AdelicVectorBundle.Minima.Absolute.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.LineVector
import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import ArakelovGeometry.AdelicVectorBundle.Minima.PositiveAtoms
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Native.Degree
import Mathlib.CategoryTheory.Category.Init

/-!
# Absolute first minima on ordinary regularity branches

Common density gives the ordinary comparison on the actual closure bundle.
On a countable discrete original base, canonical native rank-one degrees
give the comparison without assuming regularity of the closure place space.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

variable {K E : Type*} [Field K] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Source4.3.72's absolute inequality under original common countable density. -/
theorem absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlope
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    V.absoluteMaximalLogarithmicMinimum (hreg := ⟨(Or.inl hcount)⟩) ≤
      V.absoluteMaximalSlope := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  change (V.ordinaryScalarExtension (L := AlgebraicClosure K)
    (hreg := ⟨(Or.inl hcount)⟩)).maximalLogarithmicMinimum ≤ _
  rw [V.ordinaryScalarExtension_eq_common (hreg := ⟨(Or.inl hcount)⟩)]
  exact (V.scalarExtension).maximalLogarithmicMinimum_le_maximalSlope
    (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := AlgebraicClosure K)))⟩)
    (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := AlgebraicClosure K))⟩)

variable [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- The actual native line over any algebraically closed algebraic extension
has its ambient vector degree, using the produced measurable determinant. -/
theorem nativeRestrictionDegreeOfCountableDiscreteBase_span_singleton
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (s : {x : L ⊗[K] V // x ≠ 0}) :
    V.nativeRestrictionDegreeOfCountableDiscreteBase (L ∙ s.val) =
      (V.scalarExtensionOfCountableDiscreteBase).vectorDegree s := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let R := V.scalarExtensionRestrictionOfCountableDiscreteBase (L ∙ s.val)
  let hdet := V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
    (L ∙ s.val)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let u : {x : L ∙ s.val // x ≠ 0} :=
    ⟨⟨s.val, Submodule.mem_span_singleton_self s.val⟩, by
      intro h
      exact s.property (congrArg Subtype.val h)⟩
  change R.degreeOfMeasurableDeterminant (hdet := hdet) (hN := ⟨hLN⟩) = _
  rw [R.degreeOfMeasurableDeterminant_eq_vectorDegree_of_finrank_one (hdet := hdet) (hN := ⟨hLN⟩)
    (finrank_span_singleton s.property) u]
  rfl

/-- Every nonzero actual closure vector supplies a rank-one term of the
native maximal-slope supremum. -/
theorem vectorDegree_discreteScalarBundle_le_absoluteMaximalSlopeOfCountableDiscreteBase
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (s : {x : AlgebraicClosure K ⊗[K] V // x ≠ 0}) :
    ((V.scalarExtensionOfCountableDiscreteBase).vectorDegree s : EReal) ≤
      V.absoluteMaximalSlopeOfCountableDiscreteBase := by
  have h := V.nativeMean_le_absoluteMaximalSlopeOfCountableDiscreteBase
    (AlgebraicClosure K ∙ s.val) (by rw [finrank_span_singleton s.property]; exact zero_lt_one)
  rw [finrank_span_singleton s.property, Nat.cast_one, EReal.coe_one, div_one,
    V.nativeRestrictionDegreeOfCountableDiscreteBase_span_singleton s] at h
  exact h

/-- The genuine closure first minimum is bounded by all actual positive-rank
native means, with bottom conventions in ambient rank zero. -/
theorem
    maximalLogarithmicMinimum_discreteScalarBundle_le_absoluteMaximalSlopeOfCountableDiscreteBase
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    (V.scalarExtensionOfCountableDiscreteBase (L := AlgebraicClosure K)
).maximalLogarithmicMinimum ≤ V.absoluteMaximalSlopeOfCountableDiscreteBase := by
  let W := V.scalarExtensionOfCountableDiscreteBase (L := AlgebraicClosure K)
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨f, _, hf⟩ := (W.le_finrank_degreeThresholdSpan_iff 1 t).mp ht
  exact (EReal.coe_le_coe_iff.mpr (hf 0)).trans
    (V.vectorDegree_discreteScalarBundle_le_absoluteMaximalSlopeOfCountableDiscreteBase (f 0))

/-- The countable-discrete absolute inequality of source4.3.72 uses the
actual original absolute minimum and the full native closure supremum. -/
theorem absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfCountableDiscreteBase
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    V.absoluteMaximalLogarithmicMinimum
      (hreg := ⟨(Or.inr (Or.inl ⟨inferInstance, inferInstance⟩))⟩) ≤
        V.absoluteMaximalSlopeOfCountableDiscreteBase := by
  change (V.ordinaryScalarExtension (L := AlgebraicClosure K)
    (hreg := ⟨(Or.inr (Or.inl ⟨inferInstance, inferInstance⟩))⟩)).maximalLogarithmicMinimum ≤ _
  rw [V.ordinaryScalarExtension_eq_discrete]
  exact
    maximalLogarithmicMinimum_discreteScalarBundle_le_absoluteMaximalSlopeOfCountableDiscreteBase
      V

end ArakelovGeometry.AdelicVectorBundle

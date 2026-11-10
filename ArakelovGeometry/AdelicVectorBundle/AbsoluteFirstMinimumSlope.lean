/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeometricFirstMinimumSlope
import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariantsDiscrete

/-!
# Absolute first minima on ordinary regularity branches

Common density gives the ordinary comparison on the actual closure bundle.
On a countable discrete original base, canonical native rank-one degrees
give the comparison without assuming regularity of the closure place space.
-/

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

variable {K E : Type*} [Field K] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Source4.3.72's absolute inequality under original common countable density. -/
theorem absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlope
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.absoluteMaximalLogarithmicMinimum (Or.inl hcount) hN ≤
      V.absoluteMaximalSlope hcount hN := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S (AlgebraicClosure K)
  change (V.ordinaryScalarExtension (L := AlgebraicClosure K)
    (Or.inl hcount) hN).maximalLogarithmicMinimum ≤ _
  rw [V.ordinaryScalarExtension_eq_common (Or.inl hcount) hN hcount]
  exact (V.scalarExtension hcount hN).maximalLogarithmicMinimum_le_maximalSlope
    (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := AlgebraicClosure K)))
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := AlgebraicClosure K) hN)

variable [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- The actual native line over any algebraically closed algebraic extension
has its ambient vector degree, using the produced measurable determinant. -/
theorem nativeRestrictionDegreeOfCountableDiscreteBase_span_singleton
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (s : {x : L ⊗[K] E // x ≠ 0}) :
    V.nativeRestrictionDegreeOfCountableDiscreteBase hN (L ∙ s.val) =
      (V.scalarExtensionOfCountableDiscreteBase hN).vectorDegree s := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let R := V.scalarExtensionRestrictionOfCountableDiscreteBase hN (L ∙ s.val)
  let hdet := V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
    hN (L ∙ s.val)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let u : {x : L ∙ s.val // x ≠ 0} :=
    ⟨⟨s.val, Submodule.mem_span_singleton_self s.val⟩, by
      intro h
      exact s.property (congrArg Subtype.val h)⟩
  change R.degreeOfMeasurableDeterminant hdet hLN = _
  rw [R.degreeOfMeasurableDeterminant_eq_vectorDegree_of_finrank_one hdet hLN
    (finrank_span_singleton s.property) u]
  rfl

/-- Every nonzero actual closure vector supplies a rank-one term of the
native maximal-slope supremum. -/
theorem vectorDegree_discreteScalarBundle_le_absoluteMaximalSlopeOfCountableDiscreteBase
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (s : {x : AlgebraicClosure K ⊗[K] E // x ≠ 0}) :
    ((V.scalarExtensionOfCountableDiscreteBase hN).vectorDegree s : EReal) ≤
      V.absoluteMaximalSlopeOfCountableDiscreteBase hN := by
  have h := V.nativeMean_le_absoluteMaximalSlopeOfCountableDiscreteBase hN
    (AlgebraicClosure K ∙ s.val) (by rw [finrank_span_singleton s.property]; exact zero_lt_one)
  rw [finrank_span_singleton s.property, Nat.cast_one, EReal.coe_one, div_one,
    V.nativeRestrictionDegreeOfCountableDiscreteBase_span_singleton hN s] at h
  exact h

/-- The genuine closure first minimum is bounded by all actual positive-rank
native means, with bottom conventions in ambient rank zero. -/
theorem
    maximalLogarithmicMinimum_discreteScalarBundle_le_absoluteMaximalSlopeOfCountableDiscreteBase
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.scalarExtensionOfCountableDiscreteBase (L := AlgebraicClosure K)
      hN).maximalLogarithmicMinimum ≤ V.absoluteMaximalSlopeOfCountableDiscreteBase hN := by
  let W := V.scalarExtensionOfCountableDiscreteBase (L := AlgebraicClosure K) hN
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨f, _, hf⟩ := (W.le_finrank_degreeThresholdSpan_iff 1 t).mp ht
  exact (EReal.coe_le_coe_iff.mpr (hf 0)).trans
    (V.vectorDegree_discreteScalarBundle_le_absoluteMaximalSlopeOfCountableDiscreteBase hN (f 0))

/-- The countable-discrete absolute inequality of source4.3.72 uses the
actual original absolute minimum and the full native closure supremum. -/
theorem absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfCountableDiscreteBase
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.absoluteMaximalLogarithmicMinimum
      (Or.inr (Or.inl ⟨inferInstance, inferInstance⟩)) hN ≤
        V.absoluteMaximalSlopeOfCountableDiscreteBase hN := by
  change (V.ordinaryScalarExtension (L := AlgebraicClosure K)
    (Or.inr (Or.inl ⟨inferInstance, inferInstance⟩)) hN).maximalLogarithmicMinimum ≤ _
  rw [V.ordinaryScalarExtension_eq_discrete _ hN]
  exact
    maximalLogarithmicMinimum_discreteScalarBundle_le_absoluteMaximalSlopeOfCountableDiscreteBase
      V hN

end ArakelovGeometry.AdelicVectorBundle

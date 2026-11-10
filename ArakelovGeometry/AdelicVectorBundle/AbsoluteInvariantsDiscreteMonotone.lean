/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariantsDiscrete
import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminantContraction

/-!
# Original invariants bounded by actual countable discrete absolute invariants

Every original subspace gives its actual tensor extension. The genuine completed
contraction compares the produced measurable determinant degrees; the suprema
then compare the original and absolute positive degrees and maximal slopes.
-/

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v w wL
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- The genuine tensor inclusion contraction bounds every original restricted
degree by the actual native target determinant degree, without target regularity. -/
theorem degree_restrict_le_nativeRestrictionDegreeOfCountableDiscreteBase
    {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule K E) :
    (V.restrictOfMeasurableBase A (Or.inl inferInstance)).degree (Or.inl inferInstance) hN ≤
      V.nativeRestrictionDegreeOfCountableDiscreteBase hN (A.baseChange L) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let B := V.restrictOfMeasurableBase A (Or.inl inferInstance)
  let W := B.scalarExtensionOfCountableDiscreteBase (L := L) hN
  let R := V.scalarExtensionRestrictionOfCountableDiscreteBase hN (A.baseChange L)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  have he : W.degreeOfMeasurableDeterminant
      (B.scalarExtensionOfCountableDiscreteBase_determinant_isMeasurable hN) hLN ≤
      R.degreeOfMeasurableDeterminant
        (V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
          hN (A.baseChange L)) hLN :=
    W.degreeOfMeasurableDeterminant_le_of_completed_contraction R
      (Submodule.toBaseChange.toLinearEquiv L A) _ _ hLN
      (fun x z ↦ V.toNormFamily.scalarExtension_restrict_norm_le A x z)
  exact (B.degreeOfMeasurableDeterminant_scalarExtensionOfCountableDiscreteBase
    (L := L) hN).symm.le.trans he

/-- The actual original and native mean degrees compare using their unchanged
rank. The real rank-zero division convention is retained. -/
theorem slope_restrict_le_nativeMeanOfCountableDiscreteBase
    {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule K E) :
    (V.restrictOfMeasurableBase A (Or.inl inferInstance)).slope (Or.inl inferInstance) hN ≤
      V.nativeRestrictionDegreeOfCountableDiscreteBase hN (A.baseChange L) /
        (Module.finrank L (A.baseChange L) : ℝ) := by
  have hr : Module.finrank L (A.baseChange L) = Module.finrank K A :=
    (Submodule.toBaseChange.toLinearEquiv L A).finrank_eq.symm.trans Module.finrank_baseChange
  change _ / (Module.finrank K A : ℝ) ≤ _ / _
  rw [hr]
  exact div_le_div_of_nonneg_right
    (V.degree_restrict_le_nativeRestrictionDegreeOfCountableDiscreteBase hN A)
    (Nat.cast_nonneg _)

/-- Taking ALL original subspaces and their actual closure images compares
positive degree with the genuine absolute supremum. -/
theorem positiveDegree_le_absolutePositiveDegreeOfCountableDiscreteBase
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.positiveDegree (Or.inl inferInstance) hN ≤
      V.absolutePositiveDegreeOfCountableDiscreteBase hN := by
  apply V.positiveDegree_le (Or.inl inferInstance) hN
  intro A
  exact (EReal.coe_le_coe_iff.mpr
    (V.degree_restrict_le_nativeRestrictionDegreeOfCountableDiscreteBase
      (L := AlgebraicClosure K) hN A)).trans
    (V.nativeRestrictionDegree_le_absolutePositiveDegreeOfCountableDiscreteBase hN
      (A.baseChange (AlgebraicClosure K)))

/-- Positive-rank original subspaces extend with unchanged positive rank, so
their actual mean degrees bound the original maximal-slope supremum. -/
theorem maximalSlope_le_absoluteMaximalSlopeOfCountableDiscreteBase
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.maximalSlope (Or.inl inferInstance) hN ≤
      V.absoluteMaximalSlopeOfCountableDiscreteBase hN := by
  apply V.maximalSlope_le (Or.inl inferInstance) hN
  intro A hA
  have hr : Module.finrank (AlgebraicClosure K) (A.baseChange (AlgebraicClosure K)) =
      Module.finrank K A :=
    (Submodule.toBaseChange.toLinearEquiv (AlgebraicClosure K) A).finrank_eq.symm.trans
      Module.finrank_baseChange
  exact (EReal.coe_le_coe_iff.mpr
    (V.slope_restrict_le_nativeMeanOfCountableDiscreteBase
      (L := AlgebraicClosure K) hN A)).trans
    (V.nativeMean_le_absoluteMaximalSlopeOfCountableDiscreteBase hN
      (A.baseChange (AlgebraicClosure K)) (hr.symm ▸ hA))

/-- Every actual original restricted degree is bounded by the genuine
absolute positive degree; no caller-supplied native degree bound is used. -/
theorem degree_restrict_le_absolutePositiveDegreeOfCountableDiscreteBase
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule K E) :
    ((V.restrictOfMeasurableBase A (Or.inl inferInstance)).degree
      (Or.inl inferInstance) hN : EReal) ≤
      V.absolutePositiveDegreeOfCountableDiscreteBase hN :=
  (V.degree_restrict_le_positiveDegree (Or.inl inferInstance) hN A).trans
    (V.positiveDegree_le_absolutePositiveDegreeOfCountableDiscreteBase hN)

end ArakelovGeometry.AdelicVectorBundle

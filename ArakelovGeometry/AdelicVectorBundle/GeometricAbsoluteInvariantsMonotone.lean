/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeometricAbsoluteInvariants
import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminantContraction

/-!
# Actual geometric ordinary-to-absolute comparisons

Genuine completed tensor-inclusion contractions compare every original
restricted degree with its actual native closure-image degree. Taking the
actual subspace suprema gives the geometric inequalities of source4.3.67,
without countability of the original place set or target regularity.
-/

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
    (V : AdelicVectorBundle S E)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hgeo : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule K E) :
    (V.restrictOfMeasurableBase A hS).degree hS hN ≤
      V.toNormFamily.nativeAlgebraicRestrictionDegreeOfPositiveAtoms
        V.isDominated hpos hgeo (A.baseChange L) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let B := V.restrictOfMeasurableBase A hS
  let W := B.toNormFamily.algebraicScalarBundleOfPositiveAtoms (L := L)
    B.isDominated hpos hgeo
  let R := V.toNormFamily.nativeAlgebraicRestrictionOfPositiveAtoms
    V.isDominated hpos hgeo (A.baseChange L)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let hdetB := B.isMeasurable.determinant_of_discrete_or_countable hS
  let hdetR :=
    V.isDominated.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      V.toNormFamily hpos hgeo (A.baseChange L)
  have he : W.degreeOfMeasurableDeterminant hdetB.determinant_scalarExtension hLN ≤
      R.degreeOfMeasurableDeterminant hdetR hLN :=
    W.degreeOfMeasurableDeterminant_le_of_completed_contraction R
      (Submodule.toBaseChange.toLinearEquiv L A) _ _ hLN
      (fun x z => V.toNormFamily.scalarExtension_restrict_norm_le A x z)
  change B.degreeOfMeasurableDeterminant hdetB hN ≤
    R.degreeOfMeasurableDeterminant hdetR hLN
  exact (B.degreeOfMeasurableDeterminant_algebraicScalarBundleOfPositiveAtoms
    (L := L) hpos hgeo hdetB hN).symm.le.trans he

/-- The actual original and native mean degrees compare through unchanged rank. -/
theorem slope_restrict_le_nativeMeanOfPositiveAtoms
    (V : AdelicVectorBundle S E)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hgeo : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule K E) :
    (V.restrictOfMeasurableBase A hS).slope hS hN ≤
      V.toNormFamily.nativeAlgebraicRestrictionDegreeOfPositiveAtoms
        V.isDominated hpos hgeo (A.baseChange L) /
          (Module.finrank L (A.baseChange L) : ℝ) := by
  have hr : Module.finrank L (A.baseChange L) = Module.finrank K A :=
    (Submodule.toBaseChange.toLinearEquiv L A).finrank_eq.symm.trans Module.finrank_baseChange
  change _ / (Module.finrank K A : ℝ) ≤ _ / _
  rw [hr]
  exact div_le_div_of_nonneg_right
    (V.degree_restrict_le_nativeAlgebraicRestrictionDegreeOfPositiveAtoms hpos hgeo hS hN A)
    (Nat.cast_nonneg _)

/-- All original restricted degrees feed the actual geometric absolute supremum. -/
theorem positiveDegree_le_absolutePositiveDegreeOfPositiveAtoms
    (V : AdelicVectorBundle S E)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hgeo : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.positiveDegree hS hN ≤
      V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms V.isDominated hpos hgeo := by
  apply V.positiveDegree_le hS hN
  intro A
  exact (EReal.coe_le_coe_iff.mpr
    (V.degree_restrict_le_nativeAlgebraicRestrictionDegreeOfPositiveAtoms
      (L := AlgebraicClosure K) hpos hgeo hS hN A)).trans
    (V.toNormFamily.nativeRestrictionDegree_le_absolutePositiveDegreeOfPositiveAtoms
      V.isDominated hpos hgeo (A.baseChange (AlgebraicClosure K)))

/-- Positive-rank original subspaces supply actual positive-rank native mean terms. -/
theorem maximalSlope_le_absoluteMaximalSlopeOfPositiveAtoms
    (V : AdelicVectorBundle S E)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hgeo : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.maximalSlope hS hN ≤
      V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms V.isDominated hpos hgeo := by
  apply V.maximalSlope_le hS hN
  intro A hA
  have hr : Module.finrank (AlgebraicClosure K) (A.baseChange (AlgebraicClosure K)) =
      Module.finrank K A :=
    (Submodule.toBaseChange.toLinearEquiv (AlgebraicClosure K) A).finrank_eq.symm.trans
      Module.finrank_baseChange
  exact (EReal.coe_le_coe_iff.mpr
    (V.slope_restrict_le_nativeMeanOfPositiveAtoms
      (L := AlgebraicClosure K) hpos hgeo hS hN A)).trans
    (V.toNormFamily.nativeMean_le_absoluteMaximalSlopeOfPositiveAtoms V.isDominated hpos hgeo
      (A.baseChange (AlgebraicClosure K)) (hr.symm ▸ hA))

/-- Every actual original restricted degree is bounded by the geometric absolute degree. -/
theorem degree_restrict_le_absolutePositiveDegreeOfPositiveAtoms
    (V : AdelicVectorBundle S E)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hgeo : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule K E) :
    ((V.restrictOfMeasurableBase A hS).degree hS hN : EReal) ≤
      V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms V.isDominated hpos hgeo :=
  (V.degree_restrict_le_positiveDegree hS hN A).trans
    (V.positiveDegree_le_absolutePositiveDegreeOfPositiveAtoms hpos hgeo hS hN)

end ArakelovGeometry.AdelicVectorBundle

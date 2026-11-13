/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.PositiveAtoms.Basic
public import ArakelovGeometry.AdelicVectorBundle.Minima.Absolute.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.LineVector
import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import Mathlib.CategoryTheory.Category.Init

/-!
# Geometric absolute first minima and actual native slopes

Actual rank-one determinant normalization computes canonical native line
degrees without intermediate place-space regularity. Every actual closure
vector then contributes its degree to the positive-rank native mean supremum.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

variable {K E : Type*} [Field K] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace AdelicVectorBundle

/-- Actual measurable determinant degree in rank one is the generator's
vector degree, without a base place-space regularity premise. -/
theorem degreeOfMeasurableDeterminant_eq_vectorDegree_of_finrank_one
    (V : AdelicVectorBundle S) [hdet : V.toNormFamily.determinant.IsMeasurable]
    [hN : S.IsArchimedeanNormalized]
    (hr : Module.finrank K V = 1) (s : {x : V // x ≠ 0}) :
    V.degreeOfMeasurableDeterminant = V.vectorDegree s := by
  rw [V.degreeOfMeasurableDeterminant_eq_neg_integral
    ⟨_, determinant_single_wedge_ne_zero hr s.property⟩,
    vectorDegree, NormFamily.vectorDegree_eq_neg_integral]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω =>
    congrArg Real.log (V.toNormFamily.determinant_norm_single_wedge hr ω 1 s.val)

end AdelicVectorBundle
namespace NormFamily

variable [MeasurableSingletonClass S.Ω]

omit [S.IsProper] [MeasurableSingletonClass S.Ω] in
private theorem geometricFirstMinimum_normalization
    [hS : S.HasOnlyFinitePlaces] :
    ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion := by
  intro ω hω
  exact False.elim (hω (hS ω))

/-- The actual native line degree is the degree of its ambient scalar vector. -/
theorem nativeAlgebraicRestrictionDegreeOfPositiveAtoms_span_singleton
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    (s : {x : L ⊗[K] E // x ≠ 0}) :
    ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms (L ∙ s.val) =
      (ξ.algebraicScalarBundleOfPositiveAtoms).vectorDegree s := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let R := ξ.nativeAlgebraicRestrictionOfPositiveAtoms (L ∙ s.val)
  let hdet := hξ.scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
    ξ (L ∙ s.val)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let u : {x : L ∙ s.val // x ≠ 0} :=
    ⟨⟨s.val, Submodule.mem_span_singleton_self s.val⟩, by
      intro h
      exact s.property (congrArg Subtype.val h)⟩
  change R.degreeOfMeasurableDeterminant (hdet := hdet) (hN := ⟨hLN⟩) = _
  rw [R.degreeOfMeasurableDeterminant_eq_vectorDegree_of_finrank_one (hdet := hdet) (hN := ⟨hLN⟩)
    (finrank_span_singleton s.property) u]
  rfl

/-- Every genuine nonzero closure vector supplies a rank-one term of the
actual geometric absolute maximal-slope supremum. -/
theorem vectorDegree_algebraicScalarBundle_le_absoluteMaximalSlopeOfPositiveAtoms
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces]
    (s : {x : AlgebraicClosure K ⊗[K] E // x ≠ 0}) :
    ((ξ.algebraicScalarBundleOfPositiveAtoms).vectorDegree s : EReal) ≤
      ξ.absoluteMaximalSlopeOfPositiveAtoms := by
  have h := ξ.nativeMean_le_absoluteMaximalSlopeOfPositiveAtoms
    (AlgebraicClosure K ∙ s.val) (by rw [finrank_span_singleton s.property]; exact zero_lt_one)
  rw [finrank_span_singleton s.property, Nat.cast_one, EReal.coe_one, div_one,
    ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms_span_singleton s] at h
  exact h

/-- The actual closure first minimum is bounded by all actual native means,
including the empty rank-zero supremum. -/
theorem maximalLogarithmicMinimum_algebraicScalarBundle_le_absoluteMaximalSlopeOfPositiveAtoms
    (ξ : NormFamily S E) [hξ : ξ.IsDominated]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces] :
    (ξ.algebraicScalarBundleOfPositiveAtoms (L := AlgebraicClosure K)
       ).maximalLogarithmicMinimum ≤
      ξ.absoluteMaximalSlopeOfPositiveAtoms := by
  let V := ξ.algebraicScalarBundleOfPositiveAtoms (L := AlgebraicClosure K)
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨f, _, hf⟩ := (V.le_finrank_degreeThresholdSpan_iff 1 t).mp ht
  exact (EReal.coe_le_coe_iff.mpr (hf 0)).trans
    (ξ.vectorDegree_algebraicScalarBundle_le_absoluteMaximalSlopeOfPositiveAtoms
        (f 0))

end NormFamily
namespace AdelicVectorBundle

open NormFamily

variable [MeasurableSingletonClass S.Ω]

/-- The geometric absolute inequality in source Proposition4.3.72 on the
actual closure bundle, without any intermediate regularity premise. -/
theorem absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfPositiveAtoms
    (V : AdelicVectorBundle S)
    [hreg : S.HasRegularBase]
    [hN : S.IsArchimedeanNormalized]
    [hpos : S.HasPositiveAtoms] [hS : S.HasOnlyFinitePlaces] :
    V.absoluteMaximalLogarithmicMinimum ≤
      V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms := by
  change (V.ordinaryScalarExtension (L := AlgebraicClosure K)
).maximalLogarithmicMinimum ≤ _
  rw [V.ordinaryScalarExtension_eq_positiveAtoms]
  exact maximalLogarithmicMinimum_algebraicScalarBundle_le_absoluteMaximalSlopeOfPositiveAtoms
    V.toNormFamily

end AdelicVectorBundle
end ArakelovGeometry

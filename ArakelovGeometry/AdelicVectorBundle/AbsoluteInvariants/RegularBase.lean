/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.Ordinary.Closure
public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.PositiveAtoms.Basic

import ArakelovGeometry.AdelicVectorBundle.Minima.Absolute.FirstSlope
import ArakelovGeometry.AdelicVectorBundle.Minima.PositiveAtoms
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Canonical absolute invariants from original regularity

Every native subspace uses the actual restricted scalar norm and its canonical
measurable determinant. The three accepted constructions agree termwise.
No regularity of the closure place space or supplied degree bound is assumed.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hreg : S.HasRegularBase]
  [hN : S.IsArchimedeanNormalized]

/-- The actual native restriction, with regularity produced in each original branch. -/
abbrev scalarExtensionRestrictionOfRegularBase (A : Submodule L (L ⊗[K] V)) :
    AdelicVectorBundle (S.algebraicExtension L) where
  carrier := A
  toNormFamily := (V.toNormFamily.scalarExtension (L := L)).restrict A
  toIsAdelic := {
    isMeasurable := by
      rcases hreg.condition with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
      · exact (V.scalarExtensionRestrictionOfOrdinaryBase (hreg := ⟨(Or.inl h)⟩) A).isMeasurable
      · exact (V.scalarExtensionRestrictionOfOrdinaryBase
          (hreg := ⟨(Or.inr ⟨hc, hd⟩)⟩) A).isMeasurable
      · let := hm
        exact (V.toNormFamily.nativeAlgebraicRestrictionOfPositiveAtoms
          (hpos := ⟨hp⟩) (hS := ⟨hf⟩) A).isMeasurable
    dual_isMeasurable := by
      rcases hreg.condition with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
      · exact (V.scalarExtensionRestrictionOfOrdinaryBase
          (hreg := ⟨(Or.inl h)⟩) A).dual_isMeasurable
      · exact (V.scalarExtensionRestrictionOfOrdinaryBase
          (hreg := ⟨(Or.inr ⟨hc, hd⟩)⟩) A).dual_isMeasurable
      · let := hm
        exact (V.toNormFamily.nativeAlgebraicRestrictionOfPositiveAtoms
          (hpos := ⟨hp⟩) (hS := ⟨hf⟩) A).dual_isMeasurable
    isDominated := by
      exact (NormFamily.IsDominated.scalarExtension_isStronglyDominated
        V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike)).isDominated.restrict A
  }

@[simp]
theorem scalarExtensionRestrictionOfRegularBase_toNormFamily
    (A : Submodule L (L ⊗[K] V)) :
    (V.scalarExtensionRestrictionOfRegularBase A).toNormFamily =
      (V.toNormFamily.scalarExtension (L := L)).restrict A := rfl

open NormFamily.IsDominated in
/-- Accepted native determinant producers cover the same three original alternatives. -/
theorem scalarExtensionRestrictionOfRegularBase_determinant_isMeasurable
    (A : Submodule L (L ⊗[K] V)) :
    (V.scalarExtensionRestrictionOfRegularBase A).toNormFamily.determinant.IsMeasurable :=
    by
  rcases hreg.condition with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable
      (hreg := ⟨(Or.inl h)⟩) A
  · exact V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable
      (hreg := ⟨(Or.inr ⟨hc, hd⟩)⟩) A
  · let := hm
    exact scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      V.toNormFamily V.isDominated (hpos := ⟨hp⟩) (hS := ⟨hf⟩) A

variable [S.IsProper]

/-- Canonical degree of the genuine native bundle and its actual determinant. -/
def nativeRestrictionDegreeOfRegularBase (A : Submodule L (L ⊗[K] V)) : ℝ :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  (V.scalarExtensionRestrictionOfRegularBase A).degreeOfMeasurableDeterminant
    (hdet := (V.scalarExtensionRestrictionOfRegularBase_determinant_isMeasurable A))
    (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩)

/-- Exact common-density coherence on the same native subspace, for any regularity proof. -/
theorem nativeRestrictionDegreeOfRegularBase_eq_common
    [hc : S.HasCommonCountableDenseSubfield] (A : Submodule L (L ⊗[K] V)) :
    V.nativeRestrictionDegreeOfRegularBase A =
      V.nativeRestrictionDegreeOfOrdinaryBase (hreg := ⟨(Or.inl hc)⟩) A := rfl

/-- Exact discrete coherence, with no closure discreteness premise. -/
theorem nativeRestrictionDegreeOfRegularBase_eq_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] (A : Submodule L (L ⊗[K] V)) :
    V.nativeRestrictionDegreeOfRegularBase A =
      V.nativeRestrictionDegreeOfCountableDiscreteBase A := rfl

/-- Exact positive-atomic coherence on the actual native determinant. -/
theorem nativeRestrictionDegreeOfRegularBase_eq_positiveAtoms
    [MeasurableSingletonClass S.Ω] [S.HasPositiveAtoms] [S.HasOnlyFinitePlaces]
    (A : Submodule L (L ⊗[K] V)) :
    V.nativeRestrictionDegreeOfRegularBase A =
      V.toNormFamily.nativeAlgebraicRestrictionDegreeOfPositiveAtoms A := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Absolute positive degree uses every actual native closure subspace. -/
def absolutePositiveDegreeOfRegularBase : EReal :=
  ⨆ A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] V),
    (V.nativeRestrictionDegreeOfRegularBase A : EReal)

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Absolute maximal slope uses every actual positive-rank native closure mean. -/
def absoluteMaximalSlopeOfRegularBase : EReal :=
  ⨆ A : {A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] V) //
      0 < Module.finrank (AlgebraicClosure K) A},
    (V.nativeRestrictionDegreeOfRegularBase A.val /
      (Module.finrank (AlgebraicClosure K) A.val : ℝ) : EReal)

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absolutePositiveDegreeOfRegularBase_eq_common
    [S.HasCommonCountableDenseSubfield] :
    V.absolutePositiveDegreeOfRegularBase = V.absolutePositiveDegree := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absoluteMaximalSlopeOfRegularBase_eq_common
    [S.HasCommonCountableDenseSubfield] :
    V.absoluteMaximalSlopeOfRegularBase = V.absoluteMaximalSlope := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absolutePositiveDegreeOfRegularBase_eq_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    V.absolutePositiveDegreeOfRegularBase =
      V.absolutePositiveDegreeOfCountableDiscreteBase := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absoluteMaximalSlopeOfRegularBase_eq_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    V.absoluteMaximalSlopeOfRegularBase =
      V.absoluteMaximalSlopeOfCountableDiscreteBase := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absolutePositiveDegreeOfRegularBase_eq_positiveAtoms
    [MeasurableSingletonClass S.Ω] [S.HasPositiveAtoms] [S.HasOnlyFinitePlaces] :
    V.absolutePositiveDegreeOfRegularBase =
      V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absoluteMaximalSlopeOfRegularBase_eq_positiveAtoms
    [MeasurableSingletonClass S.Ω] [S.HasPositiveAtoms] [S.HasOnlyFinitePlaces] :
    V.absoluteMaximalSlopeOfRegularBase =
      V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- The actual zero native subspace supplies nonnegativity in every branch. -/
theorem absolutePositiveDegreeOfRegularBase_nonneg :
    0 ≤ V.absolutePositiveDegreeOfRegularBase := by
  rcases hreg.condition with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absolutePositiveDegree_nonneg (hcount := h)
  · let := hc
    let := hd
    exact V.absolutePositiveDegreeOfCountableDiscreteBase_nonneg
  · let := hm
    exact V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms_nonneg (hpos := ⟨hp⟩) (hS := ⟨hf⟩)

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- The previously produced all-native-subspace envelopes exclude positive infinity. -/
theorem absolutePositiveDegreeOfRegularBase_lt_top :
    V.absolutePositiveDegreeOfRegularBase < ⊤ := by
  rcases hreg.condition with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absolutePositiveDegree_lt_top (hcount := h)
  · let := hc
    let := hd
    exact V.absolutePositiveDegreeOfCountableDiscreteBase_lt_top
  · let := hm
    exact V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms_lt_top (hpos := ⟨hp⟩) (hS := ⟨hf⟩)

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- The actual positive-rank native means have a produced finite upper bound. -/
theorem absoluteMaximalSlopeOfRegularBase_lt_top :
    V.absoluteMaximalSlopeOfRegularBase < ⊤ := by
  rcases hreg.condition with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absoluteMaximalSlope_lt_top (hcount := h)
  · let := hc
    let := hd
    exact V.absoluteMaximalSlopeOfCountableDiscreteBase_lt_top
  · let := hm
    exact V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms_lt_top (hpos := ⟨hp⟩) (hS := ⟨hf⟩)

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Both endpoints are excluded before producing an actual real positive degree. -/
theorem exists_absolutePositiveDegreeOfRegularBase_eq_coe :
    ∃ a : ℝ, V.absolutePositiveDegreeOfRegularBase = (a : EReal) := by
  lift V.absolutePositiveDegreeOfRegularBase to ℝ using
    ⟨(V.absolutePositiveDegreeOfRegularBase_lt_top).ne,
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0)
        (V.absolutePositiveDegreeOfRegularBase_nonneg))⟩ with a
  exact ⟨a, rfl⟩

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Positive original rank gives an actual real absolute maximal slope in all branches. -/
theorem exists_absoluteMaximalSlopeOfRegularBase_eq_coe (hr : 0 < Module.finrank K V) :
    ∃ a : ℝ, V.absoluteMaximalSlopeOfRegularBase = (a : EReal) := by
  rcases hreg.condition with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.exists_absoluteMaximalSlope_eq_coe (hcount := h) hr
  · let := hc
    let := hd
    exact V.exists_absoluteMaximalSlopeOfCountableDiscreteBase_eq_coe hr
  · let := hm
    exact V.toNormFamily.exists_absoluteMaximalSlopeOfPositiveAtoms_eq_coe
      (hpos := ⟨hp⟩) (hS := ⟨hf⟩) hr

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Every actual native degree vanishes in ambient rank zero. -/
theorem absolutePositiveDegreeOfRegularBase_eq_zero_of_finrank_eq_zero
    (hr : Module.finrank K V = 0) : V.absolutePositiveDegreeOfRegularBase = 0 := by
  rcases hreg.condition with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absolutePositiveDegree_eq_zero_of_finrank_eq_zero (hcount := h) hr
  · let := hc
    let := hd
    exact V.absolutePositiveDegreeOfCountableDiscreteBase_eq_zero_of_finrank_eq_zero hr
  · let := hm
    exact V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms_eq_zero_of_finrank_eq_zero
      (hpos := ⟨hp⟩) (hS := ⟨hf⟩) hr

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Rank zero has no positive-rank native subspace, so the actual mean supremum is bottom. -/
theorem absoluteMaximalSlopeOfRegularBase_eq_bot_of_finrank_eq_zero
    (hr : Module.finrank K V = 0) : V.absoluteMaximalSlopeOfRegularBase = ⊥ := by
  rcases hreg.condition with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absoluteMaximalSlope_eq_bot_of_finrank_eq_zero (hcount := h) hr
  · let := hc
    let := hd
    exact V.absoluteMaximalSlopeOfCountableDiscreteBase_eq_bot_of_finrank_eq_zero hr
  · let := hm
    exact V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms_eq_bot_of_finrank_eq_zero
      (hpos := ⟨hp⟩) (hS := ⟨hf⟩) hr

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Source4.3.72 with a single canonical native-degree API on all original branches. -/
theorem absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfRegularBase :
    V.absoluteMaximalLogarithmicMinimum ≤
      V.absoluteMaximalSlopeOfRegularBase := by
  rcases hreg.condition with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlope (hcount := h)
  · let := hc
    let := hd
    exact V.absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfCountableDiscreteBase
  · let := hm
    exact V.absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfPositiveAtoms
      (hreg := ⟨(Or.inr (Or.inr ⟨hm, hp, hf⟩))⟩) (hpos := ⟨hp⟩) (hS := ⟨hf⟩)

end ArakelovGeometry.AdelicVectorBundle

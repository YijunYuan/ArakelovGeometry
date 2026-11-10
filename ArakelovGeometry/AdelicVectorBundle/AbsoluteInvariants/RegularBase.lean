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
  (V : AdelicVectorBundle S E)
  (hreg : S.HasCommonCountableDenseSubfield ∨
    (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
    (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The actual native restriction, with regularity produced in each original branch. -/
def scalarExtensionRestrictionOfRegularBase (A : Submodule L (L ⊗[K] E)) :
    AdelicVectorBundle (S.algebraicExtension L) A where
  toNormFamily := (V.toNormFamily.scalarExtension (L := L)).restrict A
  isMeasurable := by
    rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
    · exact (V.scalarExtensionRestrictionOfOrdinaryBase (Or.inl h) hN A).isMeasurable
    · exact (V.scalarExtensionRestrictionOfOrdinaryBase (Or.inr ⟨hc, hd⟩) hN A).isMeasurable
    · let := hm
      exact (V.toNormFamily.nativeAlgebraicRestrictionOfPositiveAtoms
        V.isDominated hp hf A).isMeasurable
  dual_isMeasurable := by
    rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
    · exact (V.scalarExtensionRestrictionOfOrdinaryBase (Or.inl h) hN A).dual_isMeasurable
    · exact (V.scalarExtensionRestrictionOfOrdinaryBase (Or.inr ⟨hc, hd⟩) hN A).dual_isMeasurable
    · let := hm
      exact (V.toNormFamily.nativeAlgebraicRestrictionOfPositiveAtoms
        V.isDominated hp hf A).dual_isMeasurable
  isDominated := by
    exact (NormFamily.IsDominated.scalarExtension_isStronglyDominated
      V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike hN)).isDominated.restrict A

@[simp]
theorem scalarExtensionRestrictionOfRegularBase_toNormFamily
    (A : Submodule L (L ⊗[K] E)) :
    (V.scalarExtensionRestrictionOfRegularBase hreg hN A).toNormFamily =
      (V.toNormFamily.scalarExtension (L := L)).restrict A := rfl

open NormFamily.IsDominated in
/-- Accepted native determinant producers cover the same three original alternatives. -/
theorem scalarExtensionRestrictionOfRegularBase_determinant_isMeasurable
    (A : Submodule L (L ⊗[K] E)) :
    (V.scalarExtensionRestrictionOfRegularBase hreg hN A).toNormFamily.determinant.IsMeasurable :=
    by
  rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable (Or.inl h) hN A
  · exact V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable
      (Or.inr ⟨hc, hd⟩) hN A
  · let := hm
    exact scalarExtension_restrict_determinant_isMeasurable_of_positive_atoms_of_isAlgClosed
      V.toNormFamily V.isDominated hp hf A

variable [S.IsProper]

/-- Canonical degree of the genuine native bundle and its actual determinant. -/
def nativeRestrictionDegreeOfRegularBase (A : Submodule L (L ⊗[K] E)) : ℝ :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  (V.scalarExtensionRestrictionOfRegularBase hreg hN A).degreeOfMeasurableDeterminant
    (V.scalarExtensionRestrictionOfRegularBase_determinant_isMeasurable hreg hN A)
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)

/-- Exact common-density coherence on the same native subspace, for any regularity proof. -/
theorem nativeRestrictionDegreeOfRegularBase_eq_common
    (hc : S.HasCommonCountableDenseSubfield) (A : Submodule L (L ⊗[K] E)) :
    V.nativeRestrictionDegreeOfRegularBase hreg hN A =
      V.nativeRestrictionDegreeOfOrdinaryBase (Or.inl hc) hN A := rfl

/-- Exact discrete coherence, with no closure discreteness premise. -/
theorem nativeRestrictionDegreeOfRegularBase_eq_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] (A : Submodule L (L ⊗[K] E)) :
    V.nativeRestrictionDegreeOfRegularBase hreg hN A =
      V.nativeRestrictionDegreeOfCountableDiscreteBase hN A := rfl

/-- Exact positive-atomic coherence on the actual native determinant. -/
theorem nativeRestrictionDegreeOfRegularBase_eq_positiveAtoms
    [MeasurableSingletonClass S.Ω] (hp : ∀ ω, 0 < S.v {ω}) (hf : ∀ ω, ω ∈ S.Ωfin)
    (A : Submodule L (L ⊗[K] E)) :
    V.nativeRestrictionDegreeOfRegularBase hreg hN A =
      V.toNormFamily.nativeAlgebraicRestrictionDegreeOfPositiveAtoms V.isDominated hp hf A := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Absolute positive degree uses every actual native closure subspace. -/
def absolutePositiveDegreeOfRegularBase : EReal :=
  ⨆ A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E),
    (V.nativeRestrictionDegreeOfRegularBase hreg hN A : EReal)

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Absolute maximal slope uses every actual positive-rank native closure mean. -/
def absoluteMaximalSlopeOfRegularBase : EReal :=
  ⨆ A : {A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E) //
      0 < Module.finrank (AlgebraicClosure K) A},
    (V.nativeRestrictionDegreeOfRegularBase hreg hN A.val /
      (Module.finrank (AlgebraicClosure K) A.val : ℝ) : EReal)

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absolutePositiveDegreeOfRegularBase_eq_common
    (hc : S.HasCommonCountableDenseSubfield) :
    V.absolutePositiveDegreeOfRegularBase hreg hN = V.absolutePositiveDegree hc hN := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absoluteMaximalSlopeOfRegularBase_eq_common
    (hc : S.HasCommonCountableDenseSubfield) :
    V.absoluteMaximalSlopeOfRegularBase hreg hN = V.absoluteMaximalSlope hc hN := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absolutePositiveDegreeOfRegularBase_eq_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    V.absolutePositiveDegreeOfRegularBase hreg hN =
      V.absolutePositiveDegreeOfCountableDiscreteBase hN := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absoluteMaximalSlopeOfRegularBase_eq_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    V.absoluteMaximalSlopeOfRegularBase hreg hN =
      V.absoluteMaximalSlopeOfCountableDiscreteBase hN := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absolutePositiveDegreeOfRegularBase_eq_positiveAtoms
    [MeasurableSingletonClass S.Ω] (hp : ∀ ω, 0 < S.v {ω}) (hf : ∀ ω, ω ∈ S.Ωfin) :
    V.absolutePositiveDegreeOfRegularBase hreg hN =
      V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms V.isDominated hp hf := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
theorem absoluteMaximalSlopeOfRegularBase_eq_positiveAtoms
    [MeasurableSingletonClass S.Ω] (hp : ∀ ω, 0 < S.v {ω}) (hf : ∀ ω, ω ∈ S.Ωfin) :
    V.absoluteMaximalSlopeOfRegularBase hreg hN =
      V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms V.isDominated hp hf := rfl

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- The actual zero native subspace supplies nonnegativity in every branch. -/
theorem absolutePositiveDegreeOfRegularBase_nonneg :
    0 ≤ V.absolutePositiveDegreeOfRegularBase hreg hN := by
  rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absolutePositiveDegree_nonneg h hN
  · let := hc
    let := hd
    exact V.absolutePositiveDegreeOfCountableDiscreteBase_nonneg hN
  · let := hm
    exact V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms_nonneg V.isDominated hp hf

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- The previously produced all-native-subspace envelopes exclude positive infinity. -/
theorem absolutePositiveDegreeOfRegularBase_lt_top :
    V.absolutePositiveDegreeOfRegularBase hreg hN < ⊤ := by
  rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absolutePositiveDegree_lt_top h hN
  · let := hc
    let := hd
    exact V.absolutePositiveDegreeOfCountableDiscreteBase_lt_top hN
  · let := hm
    exact V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms_lt_top V.isDominated hp hf

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- The actual positive-rank native means have a produced finite upper bound. -/
theorem absoluteMaximalSlopeOfRegularBase_lt_top :
    V.absoluteMaximalSlopeOfRegularBase hreg hN < ⊤ := by
  rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absoluteMaximalSlope_lt_top h hN
  · let := hc
    let := hd
    exact V.absoluteMaximalSlopeOfCountableDiscreteBase_lt_top hN
  · let := hm
    exact V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms_lt_top V.isDominated hp hf

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Both endpoints are excluded before producing an actual real positive degree. -/
theorem exists_absolutePositiveDegreeOfRegularBase_eq_coe :
    ∃ a : ℝ, V.absolutePositiveDegreeOfRegularBase hreg hN = (a : EReal) := by
  lift V.absolutePositiveDegreeOfRegularBase hreg hN to ℝ using
    ⟨(V.absolutePositiveDegreeOfRegularBase_lt_top hreg hN).ne,
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0)
        (V.absolutePositiveDegreeOfRegularBase_nonneg hreg hN))⟩ with a
  exact ⟨a, rfl⟩

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Positive original rank gives an actual real absolute maximal slope in all branches. -/
theorem exists_absoluteMaximalSlopeOfRegularBase_eq_coe (hr : 0 < Module.finrank K E) :
    ∃ a : ℝ, V.absoluteMaximalSlopeOfRegularBase hreg hN = (a : EReal) := by
  rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.exists_absoluteMaximalSlope_eq_coe h hN hr
  · let := hc
    let := hd
    exact V.exists_absoluteMaximalSlopeOfCountableDiscreteBase_eq_coe hN hr
  · let := hm
    exact V.toNormFamily.exists_absoluteMaximalSlopeOfPositiveAtoms_eq_coe
      V.isDominated hp hf hr

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Every actual native degree vanishes in ambient rank zero. -/
theorem absolutePositiveDegreeOfRegularBase_eq_zero_of_finrank_eq_zero
    (hr : Module.finrank K E = 0) : V.absolutePositiveDegreeOfRegularBase hreg hN = 0 := by
  rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absolutePositiveDegree_eq_zero_of_finrank_eq_zero h hN hr
  · let := hc
    let := hd
    exact V.absolutePositiveDegreeOfCountableDiscreteBase_eq_zero_of_finrank_eq_zero hN hr
  · let := hm
    exact V.toNormFamily.absolutePositiveDegreeOfPositiveAtoms_eq_zero_of_finrank_eq_zero
      V.isDominated hp hf hr

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Rank zero has no positive-rank native subspace, so the actual mean supremum is bottom. -/
theorem absoluteMaximalSlopeOfRegularBase_eq_bot_of_finrank_eq_zero
    (hr : Module.finrank K E = 0) : V.absoluteMaximalSlopeOfRegularBase hreg hN = ⊥ := by
  rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absoluteMaximalSlope_eq_bot_of_finrank_eq_zero h hN hr
  · let := hc
    let := hd
    exact V.absoluteMaximalSlopeOfCountableDiscreteBase_eq_bot_of_finrank_eq_zero hN hr
  · let := hm
    exact V.toNormFamily.absoluteMaximalSlopeOfPositiveAtoms_eq_bot_of_finrank_eq_zero
      V.isDominated hp hf hr

omit [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Source4.3.72 with a single canonical native-degree API on all original branches. -/
theorem absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfRegularBase :
    V.absoluteMaximalLogarithmicMinimum hreg hN ≤
      V.absoluteMaximalSlopeOfRegularBase hreg hN := by
  rcases hreg with h | ⟨hc, hd⟩ | ⟨hm, hp, hf⟩
  · exact V.absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlope h hN
  · let := hc
    let := hd
    exact V.absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfCountableDiscreteBase hN
  · let := hm
    exact V.absoluteMaximalLogarithmicMinimum_le_absoluteMaximalSlopeOfPositiveAtoms
      (Or.inr (Or.inr ⟨hm, hp, hf⟩)) hN hp hf

end ArakelovGeometry.AdelicVectorBundle

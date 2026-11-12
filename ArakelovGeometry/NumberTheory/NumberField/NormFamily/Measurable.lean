/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.Basic

/-!
# Every standard number-field norm family is measurable

Chen–Moriwaki, Remark 4.1.25, on the actual standard normalized curve.
This requires no norm comparison or finite-place ultrametricity. Applying
it also to actual dual norms constructs bundles from dominated families.
-/

@[expose] public section

namespace ArakelovGeometry

open AdelicStructure
variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

/-- Every norm family on the source-standard number-field curve is measurable. -/
theorem NormFamily.isMeasurable_normalizedNumberField
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) : ξ.IsMeasurable :=
  ξ.isMeasurable_of_discrete

namespace AdelicVectorBundle
variable [FiniteDimensional K E]

/-- A dominated standard number-field family gives an actual adelic bundle. -/
noncomputable def ofDominatedNumberField
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsDominated] :
    AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E where
  toNormFamily := ξ
  isMeasurable := ξ.isMeasurable_normalizedNumberField
  dual_isMeasurable := ξ.dual.isMeasurable_normalizedNumberField
  isDominated := hξ

@[simp]
theorem ofDominatedNumberField_toNormFamily
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsDominated] :
    (ofDominatedNumberField ξ).toNormFamily = ξ := rfl

/-- Strong domination is exactly strong adelicity for the produced bundle. -/
theorem ofDominatedNumberField_isStronglyAdelic_iff
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsDominated] :
    (ofDominatedNumberField ξ).IsStronglyAdelic ↔ ξ.IsStronglyDominated := Iff.rfl

end AdelicVectorBundle
end ArakelovGeometry

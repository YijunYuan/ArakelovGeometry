/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairNorm

import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Countable
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
import ArakelovGeometry.AdelicVectorBundle.Tensor.Domination
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The actual binary mixed tensor adelic bundle

The source finite mixed tensor bundle is transported by its canonical binary
equivalence. Both measurability conditions and strong domination are proved.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- Either source base alternative produces actual binary mixed measurability. -/
theorem IsMeasurable.mixedTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    [hS : S.HasMeasurableBase] :
    (ξ.mixedTensorPair η).IsMeasurable :=
  (inferInstance : (mixedTensor (tensorPairFactors ξ η)).IsMeasurable).pullback _ _

/-- The actual mixed binary norm is strongly dominated from the two factors. -/
theorem IsDominated.strong_mixedTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsDominated) (hη : η.IsDominated)
    [hN : S.IsArchimedeanNormalized] :
    (ξ.mixedTensorPair η).IsStronglyDominated :=
  (IsDominated.strong_mixedTensor (tensorPairFactors ξ η) inferInstance
    S.v_Ωinf_lt_top_of_isRCLike).pullback _ _

end NormFamily

namespace AdelicVectorBundle

/-- The actual binary mixed tensor bundle, with its analytic properties produced. -/
abbrev mixedTensorPair (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    AdelicVectorBundle S :=
  ofMeasurableDominated (V.toNormFamily.mixedTensorPair W.toNormFamily)
    (hm := (V.isMeasurable.mixedTensorPair W.isMeasurable))
    (hd := (V.isDominated.strong_mixedTensorPair W.isDominated).isDominated)

@[simp]
theorem mixedTensorPair_toNormFamily (V : AdelicVectorBundle S)
    (W : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.mixedTensorPair W).toNormFamily =
      V.toNormFamily.mixedTensorPair W.toNormFamily := rfl

/-- The binary tensor constructor retains the actual strong adelic predicate. -/
theorem mixedTensorPair_isStronglyAdelic (V : AdelicVectorBundle S)
    (W : AdelicVectorBundle S)
    [S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.mixedTensorPair W).IsStronglyAdelic :=
  V.isDominated.strong_mixedTensorPair W.isDominated

end AdelicVectorBundle

end

end ArakelovGeometry

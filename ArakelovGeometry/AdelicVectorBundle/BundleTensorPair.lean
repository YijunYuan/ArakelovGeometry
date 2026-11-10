/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.TensorPairNorm

/-!
# The actual binary mixed tensor adelic bundle

The source finite mixed tensor bundle is transported by its canonical binary
equivalence. Both measurability conditions and strong domination are proved.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- Either source base alternative produces actual binary mixed measurability. -/
theorem IsMeasurable.mixedTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (ξ.mixedTensorPair η).IsMeasurable := by
  have hm : ∀ i, (tensorPairFactors ξ η i).IsMeasurable := by
    rintro (i | i)
    · exact hξ
    · exact hη
  exact (IsMeasurable.mixedTensor_of_discrete_or_countable _ hm hS).pullback _ _

/-- The actual mixed binary norm is strongly dominated from the two factors. -/
theorem IsDominated.strong_mixedTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsDominated) (hη : η.IsDominated)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ξ.mixedTensorPair η).IsStronglyDominated := by
  have hd : ∀ i, (tensorPairFactors ξ η i).IsDominated := by
    rintro (i | i)
    · exact hξ
    · exact hη
  exact (IsDominated.strong_mixedTensor _ hd
    (S.v_Ωinf_lt_top_of_isRCLike hN)).pullback _ _ hN

end NormFamily

namespace AdelicVectorBundle

/-- The actual binary mixed tensor bundle, with its analytic properties produced. -/
def mixedTensorPair (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    AdelicVectorBundle S (E ⊗[K] F) :=
  ofMeasurableDominated (V.toNormFamily.mixedTensorPair W.toNormFamily)
    (V.isMeasurable.mixedTensorPair W.isMeasurable hS)
    (V.isDominated.strong_mixedTensorPair W.isDominated hN).isDominated hS

@[simp]
theorem mixedTensorPair_toNormFamily (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.mixedTensorPair W hS hN).toNormFamily =
      V.toNormFamily.mixedTensorPair W.toNormFamily := rfl

/-- The binary tensor constructor retains the actual strong adelic predicate. -/
theorem mixedTensorPair_isStronglyAdelic (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.mixedTensorPair W hS hN).IsStronglyAdelic :=
  V.isDominated.strong_mixedTensorPair W.isDominated hN

end AdelicVectorBundle

end

end ArakelovGeometry

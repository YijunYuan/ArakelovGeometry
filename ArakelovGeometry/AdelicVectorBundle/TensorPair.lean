/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.BundleTensorCountable
public import ArakelovGeometry.AdelicVectorBundle.TensorOperatorBaseChange

/-!
# Binary injective tensor families

The existing finite tensor norm is transported by the canonical equivalence
to Mathlib's ordinary binary tensor product. This is the same tensor norm.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u v w

/-- The two actual factors of a binary finite tensor product. -/
abbrev BinaryTensorFactors (E F : Type w) : Unit ⊕ Unit → Type w
  | .inl _ => E
  | .inr _ => F

variable {K : Type u} [Field K] {E F : Type w}

instance binaryTensorFactorsAddCommGroup [AddCommGroup E] [AddCommGroup F]
    (i : Unit ⊕ Unit) : AddCommGroup (BinaryTensorFactors E F i) :=
  match i with
  | .inl _ => inferInstance
  | .inr _ => inferInstance

instance binaryTensorFactorsModule [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (i : Unit ⊕ Unit) : Module K (BinaryTensorFactors E F i) :=
  match i with
  | .inl _ => inferInstance
  | .inr _ => inferInstance

instance binaryTensorFactorsFiniteDimensional [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (i : Unit ⊕ Unit) : FiniteDimensional K (BinaryTensorFactors E F i) :=
  match i with
  | .inl _ => inferInstance
  | .inr _ => inferInstance

variable {S : AdelicStructure.{u, v} K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- The given two norm families, indexed as a finite family. -/
def tensorPairFactors (ξ : NormFamily S E) (η : NormFamily S F) :
    ∀ i, NormFamily S (BinaryTensorFactors E F i)
  | .inl _ => ξ
  | .inr _ => η

/-- The injective norm on the ordinary binary tensor product, transported
from the existing canonical finite tensor norm. -/
noncomputable def injectiveTensorPair (ξ : NormFamily S E) (η : NormFamily S F) :
    NormFamily S (E ⊗[K] F) :=
  (injectiveTensor (tensorPairFactors ξ η)).pullback
    (binaryTensorEquiv K (BinaryTensorFactors E F)).symm.toLinearMap
    (binaryTensorEquiv K (BinaryTensorFactors E F)).symm.injective

@[simp]
theorem injectiveTensorPair_norm_tmul (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (a : (S.ϕ ω).Completion) (z : E ⊗[K] F) :
    (ξ.injectiveTensorPair η).norm ω (a ⊗ₜ[K] z) =
      (injectiveTensor (tensorPairFactors ξ η)).norm ω
        (a ⊗ₜ[K] (binaryTensorEquiv K (BinaryTensorFactors E F)).symm z) := rfl

/-- Either source base hypothesis proves measurability of the actual binary norm. -/
theorem IsMeasurable.injectiveTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (ξ.injectiveTensorPair η).IsMeasurable := by
  have hm : ∀ i, (tensorPairFactors ξ η i).IsMeasurable := by
    rintro (i | i)
    · exact hξ
    · exact hη
  exact (IsMeasurable.injectiveTensor_of_discrete_or_countable _ hm hS).pullback _ _

/-- Domination of both factors supplies domination of the actual binary norm. -/
theorem IsDominated.injectiveTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsDominated) (hη : η.IsDominated) (hfin : S.v S.Ωinf < ⊤) :
    (ξ.injectiveTensorPair η).IsDominated := by
  have hd : ∀ i, (tensorPairFactors ξ η i).IsDominated := by
    rintro (i | i)
    · exact hξ
    · exact hη
  exact (IsDominated.strong_injectiveTensor _ hd hfin).1.pullback _ _

end NormFamily

namespace AdelicVectorBundle

/-- The actual binary injective tensor bundle, with norm and dual measurability
proved under the source alternatives. -/
noncomputable def injectiveTensorPair (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    AdelicVectorBundle S (E ⊗[K] F) :=
  ofMeasurableDominated (V.toNormFamily.injectiveTensorPair W.toNormFamily)
    (V.isMeasurable.injectiveTensorPair W.isMeasurable hS)
    (V.isDominated.injectiveTensorPair W.isDominated (S.v_Ωinf_lt_top_of_isRCLike hN)) hS

@[simp]
theorem injectiveTensorPair_toNormFamily (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.injectiveTensorPair W hS hN).toNormFamily =
      V.toNormFamily.injectiveTensorPair W.toNormFamily := rfl

end AdelicVectorBundle

end ArakelovGeometry

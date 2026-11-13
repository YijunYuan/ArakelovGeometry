/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Basic
public import ArakelovGeometry.Analysis.Tensor.Operator
public import Mathlib.Algebra.Module.ULift

import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Countable
import ArakelovGeometry.AdelicVectorBundle.Tensor.Domination
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Binary injective tensor families

The existing finite tensor norm is transported by the canonical equivalence
to Mathlib's ordinary binary tensor product. This is the same tensor norm.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u v w w'

/-- The two actual factors of a binary finite tensor product. -/
abbrev BinaryTensorFactors (E F : Type w) : Unit ⊕ Unit → Type w
  | .inl _ => E
  | .inr _ => F

section SameUniverse

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

end SameUniverse

/-- The two factors lifted to the common universe used only by the finite tensor backend. -/
abbrev LiftedTensorFactors (E : Type w) (F : Type w') : Unit ⊕ Unit → Type (max w w') :=
  BinaryTensorFactors (ULift.{w'} E) (ULift.{w} F)

variable {K : Type u} [Field K] {E : Type w} {F : Type w'}

section Algebra

variable (K E F) [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- The finite tensor of the lifted factors is canonically the original binary tensor. -/
def tensorPairEquiv : (⨂[K] i, LiftedTensorFactors E F i) ≃ₗ[K] E ⊗[K] F :=
  (binaryTensorEquiv K (LiftedTensorFactors E F)).trans
    (TensorProduct.congr ULift.moduleEquiv ULift.moduleEquiv)

@[simp]
theorem tensorPairEquiv_tprod (x : ∀ i, LiftedTensorFactors E F i) :
    tensorPairEquiv K E F (⨂ₜ[K] i, x i) =
      (x (.inl ())).down ⊗ₜ[K] (x (.inr ())).down := by
  simp [tensorPairEquiv]

end Algebra

variable {S : AdelicStructure.{u, v} K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- The given two norm families, indexed as a finite family. -/
noncomputable def tensorPairFactors (ξ : NormFamily S E) (η : NormFamily S F) :
    ∀ i, NormFamily S (LiftedTensorFactors E F i)
  | .inl _ => ξ.pullback ULift.moduleEquiv.toLinearMap ULift.moduleEquiv.injective
  | .inr _ => η.pullback ULift.moduleEquiv.toLinearMap ULift.moduleEquiv.injective

omit [FiniteDimensional K E] [FiniteDimensional K F] in
instance instIsMeasurableTensorPairFactors (ξ : NormFamily S E) (η : NormFamily S F)
    [hξ : ξ.IsMeasurable] [hη : η.IsMeasurable] (i : Unit ⊕ Unit) :
    (tensorPairFactors ξ η i).IsMeasurable :=
  match i with
  | .inl _ => hξ.pullback _ ULift.moduleEquiv.injective
  | .inr _ => hη.pullback _ ULift.moduleEquiv.injective

instance instIsDominatedTensorPairFactors (ξ : NormFamily S E) (η : NormFamily S F)
    [hξ : ξ.IsDominated] [hη : η.IsDominated] (i : Unit ⊕ Unit) :
    (tensorPairFactors ξ η i).IsDominated :=
  match i with
  | .inl _ => hξ.pullback _ ULift.moduleEquiv.injective
  | .inr _ => hη.pullback _ ULift.moduleEquiv.injective

/-- The injective norm on the ordinary binary tensor product, transported
from the existing canonical finite tensor norm. -/
noncomputable def injectiveTensorPair (ξ : NormFamily S E) (η : NormFamily S F) :
    NormFamily S (E ⊗[K] F) :=
  (injectiveTensor (tensorPairFactors ξ η)).pullback
    (tensorPairEquiv K E F).symm.toLinearMap
    (tensorPairEquiv K E F).symm.injective

instance instIsUltrametricInjectiveTensorPair (ξ : NormFamily S E) (η : NormFamily S F) :
    (ξ.injectiveTensorPair η).IsUltrametric :=
  (injectiveTensor_isUltrametric (tensorPairFactors ξ η)).pullback
    (tensorPairEquiv K E F).symm.toLinearMap
    (tensorPairEquiv K E F).symm.injective

@[simp]
theorem injectiveTensorPair_norm_tmul (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (a : (S.ϕ ω).Completion) (z : E ⊗[K] F) :
    (ξ.injectiveTensorPair η).norm ω (a ⊗ₜ[K] z) =
      (injectiveTensor (tensorPairFactors ξ η)).norm ω
        (a ⊗ₜ[K] (tensorPairEquiv K E F).symm z) := rfl

/-- Either source base hypothesis proves measurability of the actual binary norm. -/
theorem IsMeasurable.injectiveTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    [hS : S.HasMeasurableBase] :
    (ξ.injectiveTensorPair η).IsMeasurable :=
  (inferInstance : (injectiveTensor (tensorPairFactors ξ η)).IsMeasurable).pullback _ _

/-- Domination of both factors supplies domination of the actual binary norm. -/
theorem IsDominated.injectiveTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsDominated) (hη : η.IsDominated) (hfin : S.v S.Ωinf < ⊤) :
    (ξ.injectiveTensorPair η).IsDominated :=
  (IsDominated.strong_injectiveTensor (tensorPairFactors ξ η) inferInstance hfin).1.pullback _ _

end NormFamily

namespace AdelicVectorBundle

/-- The actual binary injective tensor bundle, with norm and dual measurability
proved under the source alternatives. -/
noncomputable abbrev injectiveTensorPair (V : AdelicVectorBundle.{w} S)
    (W : AdelicVectorBundle.{w'} S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    AdelicVectorBundle S :=
  ofMeasurableDominated (V.toNormFamily.injectiveTensorPair W.toNormFamily)
    (hm := (V.isMeasurable.injectiveTensorPair W.isMeasurable))
    (hd := (V.isDominated.injectiveTensorPair W.isDominated (by exact S.v_Ωinf_lt_top_of_isRCLike)))

@[simp]
theorem injectiveTensorPair_toNormFamily (V : AdelicVectorBundle.{w} S)
    (W : AdelicVectorBundle.{w'} S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.injectiveTensorPair W).toNormFamily =
      V.toNormFamily.injectiveTensorPair W.toNormFamily := rfl

end AdelicVectorBundle

end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.InnerProduct
public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairNorm

import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Countable
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The actual binary Hermitian tensor family

The existing finite orthogonal tensor norm is transported by the same
canonical binary tensor equivalence as the injective and mixed families.
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

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Hermitianity of the two original norm families on their canonical
finite binary indexing family. -/
theorem IsHermitian.tensorPairFactors {ξ : NormFamily S E} {η : NormFamily S F}
    [hN : S.IsArchimedeanNormalized]
    (hξ : ξ.IsHermitian) (hη : η.IsHermitian) :
    ∀ i, (tensorPairFactors ξ η i).IsHermitian := by
  rintro (i | i)
  · exact hξ.pullback _ ULift.moduleEquiv.injective
  · exact hη.pullback _ ULift.moduleEquiv.injective

omit [FiniteDimensional K E] [FiniteDimensional K F] in
instance instIsHermitianTensorPairFactors (ξ : NormFamily S E) (η : NormFamily S F)
    [S.IsArchimedeanNormalized] [ξ.IsHermitian] [η.IsHermitian] (i : Unit ⊕ Unit) :
    (tensorPairFactors ξ η i).IsHermitian :=
  IsHermitian.tensorPairFactors inferInstance inferInstance i

/-- The actual orthogonal norm on the ordinary binary tensor product. -/
def orthogonalTensorPair (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] :
    NormFamily S (E ⊗[K] F) :=
  (orthogonalTensor (tensorPairFactors ξ η)).pullback
    (tensorPairEquiv K E F).symm.toLinearMap
    (tensorPairEquiv K E F).symm.injective

@[inherit_doc ArakelovGeometry.NormFamily.orthogonalTensorPair]
scoped[TensorProduct] infixl:100 " ⊗ʰ " => ArakelovGeometry.NormFamily.orthogonalTensorPair

/-- The actual binary orthogonal norm is between the injective and
projective norms on every completed vector. -/
theorem orthogonalTensorPair_norm_bounds (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ξ.injectiveTensorPair η).norm ω z ≤ (ξ ⊗ʰ η).norm ω z ∧
      (ξ ⊗ʰ η).norm ω z ≤ (ξ.projectiveTensorPair η).norm ω z :=
  orthogonalTensor_norm_bounds (tensorPairFactors ξ η) ω _

/-- The actual binary orthogonal tensor norm equals the injective tensor
norm at finite places. -/
theorem orthogonalTensorPair_norm_of_finite (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ξ ⊗ʰ η).norm ω z = (ξ.injectiveTensorPair η).norm ω z :=
  orthogonalTensor_norm_of_finite (tensorPairFactors ξ η) ω hω _

/-- The actual completed norm and scalar action satisfy Hermitianity. -/
theorem orthogonalTensorPair_isHermitian (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] :
    (ξ ⊗ʰ η).IsHermitian :=
  (orthogonalTensor_isHermitian (tensorPairFactors ξ η)).pullback _ _

/-- Either exact source alternative supplies binary orthogonal measurability. -/
theorem IsMeasurable.orthogonalTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [ξ.IsHermitian] [η.IsHermitian] :
    (ξ ⊗ʰ η).IsMeasurable :=
  (inferInstance : (orthogonalTensor (tensorPairFactors ξ η)).IsMeasurable).pullback _ _

/-- The original factor domination produces actual strong tensor domination. -/
theorem IsDominated.strong_orthogonalTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsDominated) (hη : η.IsDominated)
    [hN : S.IsArchimedeanNormalized]
    [ξ.IsHermitian] [η.IsHermitian] :
    (ξ ⊗ʰ η).IsStronglyDominated :=
  (inferInstance : (orthogonalTensor (tensorPairFactors ξ η)).IsStronglyDominated).pullback _ _

/-- The binary orthogonal pure-tensor formula holds on arbitrary actual
completed vectors, including zero factors and zero-dimensional spaces. -/
theorem orthogonalTensorPair_norm_tmul_completed (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ ⊗ʰ η).norm ω
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
        (x ⊗ₜ[(S.ϕ ω).Completion] y)) = ξ.norm ω x * η.norm ω y := by
  let X : ∀ i, (S.ϕ ω).Completion ⊗[K] LiftedTensorFactors E F i :=
    fun i ↦ match i with
      | .inl _ => (ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _).symm x
      | .inr _ => (ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _).symm y
  have hz : (tensorPairEquiv K E F).symm.toLinearMap.baseChange
      (S.ϕ ω).Completion
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
        (x ⊗ₜ[(S.ϕ ω).Completion] y)) =
      (tensorBaseChangeEquiv K (S.ϕ ω).Completion (LiftedTensorFactors E F)).symm
        (⨂ₜ[(S.ϕ ω).Completion] i, X i) := by
    apply (tensorBaseChangeEquiv K (S.ϕ ω).Completion (LiftedTensorFactors E F)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact tensorBaseChangeEquiv_binary_symm_tmul K (S.ϕ ω).Completion E F x y
  change (orthogonalTensor (tensorPairFactors ξ η)).norm ω _ = _
  rw [hz]
  have h := orthogonalTensor_norm_tprod (tensorPairFactors ξ η) ω X
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, tensorPairFactors, X,
    pullback_norm] at h
  change _ = ξ.norm ω ((ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _)
      ((ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _).symm x)) *
    η.norm ω ((ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _)
      ((ULift.moduleEquiv.baseChange K (S.ϕ ω).Completion _ _).symm y)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- The actual dual tensor measurability is produced, rather than assumed. -/
theorem IsMeasurable.orthogonalTensorPair_dual {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [ξ.IsHermitian] [η.IsHermitian] :
    (ξ ⊗ʰ η).dual.IsMeasurable :=
  (hξ.orthogonalTensorPair hη).dual_of_discrete_or_countable

instance instIsMeasurableOrthogonalTensorPair (ξ : NormFamily S E) (η : NormFamily S F)
    [S.NormMeasurabilityHypotheses] [S.IsArchimedeanNormalized]
    [ξ.IsMeasurable] [η.IsMeasurable] [ξ.IsHermitian] [η.IsHermitian] :
    (ξ ⊗ʰ η).IsMeasurable :=
  IsMeasurable.orthogonalTensorPair inferInstance inferInstance

instance instIsStronglyDominatedOrthogonalTensorPair (ξ : NormFamily S E) (η : NormFamily S F)
    [S.IsArchimedeanNormalized] [ξ.IsDominated] [η.IsDominated]
    [ξ.IsHermitian] [η.IsHermitian] : (ξ ⊗ʰ η).IsStronglyDominated :=
  IsDominated.strong_orthogonalTensorPair inferInstance inferInstance

end NormFamily

namespace AdelicVectorBundle

/-- The actual binary Hermitian tensor bundle, with its analytic properties
produced from the factors and the source measurability alternatives. -/
abbrev orthogonalTensorPair (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.IsHermitian] [hW : W.IsHermitian] :
    AdelicVectorBundle S :=
  ofMeasurableDominated (V.toNormFamily ⊗ʰ W.toNormFamily)

@[inherit_doc ArakelovGeometry.AdelicVectorBundle.orthogonalTensorPair]
scoped[TensorProduct] infixl:100 " ⊗ʰ " => ArakelovGeometry.AdelicVectorBundle.orthogonalTensorPair

@[simp]
theorem orthogonalTensorPair_toNormFamily (V : AdelicVectorBundle S)
    (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.IsHermitian] [hW : W.IsHermitian] :
    (V ⊗ʰ W).toNormFamily =
      V.toNormFamily.orthogonalTensorPair W.toNormFamily := rfl

/-- The canonical tensor bundle is strongly adelic in its actual norms. -/
theorem orthogonalTensorPair_isStronglyAdelic (V : AdelicVectorBundle S)
    (W : AdelicVectorBundle S)
    [S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.IsHermitian] [hW : W.IsHermitian] :
    (V ⊗ʰ W).IsStronglyAdelic :=
  V.isDominated.strong_orthogonalTensorPair W.isDominated

/-- The actual binary tensor bundle has the orthogonal product inner norm. -/
theorem orthogonalTensorPair_isHermitian (V : AdelicVectorBundle S)
    (W : AdelicVectorBundle S)
    [S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.IsHermitian] [hW : W.IsHermitian] :
    (V ⊗ʰ W).IsHermitian :=
  NormFamily.orthogonalTensorPair_isHermitian _ _

end AdelicVectorBundle

end

end ArakelovGeometry

namespace ArakelovGeometry.AdelicVectorBundle
attribute [instance] orthogonalTensorPair_isHermitian orthogonalTensorPair_isStronglyAdelic
end ArakelovGeometry.AdelicVectorBundle

namespace ArakelovGeometry.NormFamily
attribute [instance] orthogonalTensorPair_isHermitian
end ArakelovGeometry.NormFamily

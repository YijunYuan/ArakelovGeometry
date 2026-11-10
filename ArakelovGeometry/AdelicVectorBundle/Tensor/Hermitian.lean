/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.HermitianInnerProduct
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

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Hermitianity of the two original norm families on their canonical
finite binary indexing family. -/
theorem IsHermitian.tensorPairFactors {ξ : NormFamily S E} {η : NormFamily S F}
    {hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN) :
    ∀ i, (tensorPairFactors ξ η i).IsHermitian hN := by
  rintro (i | i)
  · exact hξ
  · exact hη

/-- The actual orthogonal norm on the ordinary binary tensor product. -/
def orthogonalTensorPair (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN) :
    NormFamily S (E ⊗[K] F) :=
  (orthogonalTensor (tensorPairFactors ξ η) hN (hξ.tensorPairFactors hη)).pullback
    (binaryTensorEquiv K (BinaryTensorFactors E F)).symm.toLinearMap
    (binaryTensorEquiv K (BinaryTensorFactors E F)).symm.injective

/-- The actual binary orthogonal norm is between the injective and
projective norms on every completed vector. -/
theorem orthogonalTensorPair_norm_bounds (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ξ.injectiveTensorPair η).norm ω z ≤ (ξ.orthogonalTensorPair η hN hξ hη).norm ω z ∧
      (ξ.orthogonalTensorPair η hN hξ hη).norm ω z ≤ (ξ.projectiveTensorPair η).norm ω z :=
  orthogonalTensor_norm_bounds (tensorPairFactors ξ η) hN (hξ.tensorPairFactors hη) ω _

/-- The actual binary orthogonal tensor norm equals the injective tensor
norm at finite places. -/
theorem orthogonalTensorPair_norm_of_finite (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ξ.orthogonalTensorPair η hN hξ hη).norm ω z = (ξ.injectiveTensorPair η).norm ω z :=
  orthogonalTensor_norm_of_finite (tensorPairFactors ξ η) hN (hξ.tensorPairFactors hη) ω hω _

/-- The actual completed norm and scalar action satisfy Hermitianity. -/
theorem orthogonalTensorPair_isHermitian (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN) :
    (ξ.orthogonalTensorPair η hN hξ hη).IsHermitian hN :=
  (orthogonalTensor_isHermitian (tensorPairFactors ξ η) hN
    (hξ.tensorPairFactors hη)).pullback _ _

/-- Either exact source alternative supplies binary orthogonal measurability. -/
theorem IsMeasurable.orthogonalTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hHξ : ξ.IsHermitian hN) (hHη : η.IsHermitian hN) :
    (ξ.orthogonalTensorPair η hN hHξ hHη).IsMeasurable := by
  have hm : ∀ i, (tensorPairFactors ξ η i).IsMeasurable := by
    rintro (i | i)
    · exact hξ
    · exact hη
  exact (IsMeasurable.orthogonalTensor_of_discrete_or_countable _ hN
    (hHξ.tensorPairFactors hHη) hm hS).pullback _ _

/-- The original factor domination produces actual strong tensor domination. -/
theorem IsDominated.strong_orthogonalTensorPair {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsDominated) (hη : η.IsDominated)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hHξ : ξ.IsHermitian hN) (hHη : η.IsHermitian hN) :
    (ξ.orthogonalTensorPair η hN hHξ hHη).IsStronglyDominated := by
  have hd : ∀ i, (tensorPairFactors ξ η i).IsDominated := by
    rintro (i | i)
    · exact hξ
    · exact hη
  exact (IsDominated.strong_orthogonalTensor _ hN (hHξ.tensorPairFactors hHη) hd).pullback
    _ _ hN

/-- The binary orthogonal pure-tensor formula holds on arbitrary actual
completed vectors, including zero factors and zero-dimensional spaces. -/
theorem orthogonalTensorPair_norm_tmul_completed (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.orthogonalTensorPair η hN hξ hη).norm ω
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
        (x ⊗ₜ[(S.ϕ ω).Completion] y)) = ξ.norm ω x * η.norm ω y := by
  let X : ∀ i, (S.ϕ ω).Completion ⊗[K] BinaryTensorFactors E F i :=
    fun i ↦ match i with | .inl _ => x | .inr _ => y
  have hz : (binaryTensorEquiv K (BinaryTensorFactors E F)).symm.toLinearMap.baseChange
      (S.ϕ ω).Completion
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
        (x ⊗ₜ[(S.ϕ ω).Completion] y)) =
      (tensorBaseChangeEquiv K (S.ϕ ω).Completion (BinaryTensorFactors E F)).symm
        (⨂ₜ[(S.ϕ ω).Completion] i, X i) := by
    apply (tensorBaseChangeEquiv K (S.ϕ ω).Completion (BinaryTensorFactors E F)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact tensorBaseChangeEquiv_binary_symm_tmul K (S.ϕ ω).Completion E F x y
  change (orthogonalTensor (tensorPairFactors ξ η) hN (hξ.tensorPairFactors hη)).norm ω _ = _
  rw [hz]
  have h := orthogonalTensor_norm_tprod (tensorPairFactors ξ η) hN
    (hξ.tensorPairFactors hη) ω X
  simpa only [Fintype.prod_sum_type, Fintype.prod_unique, tensorPairFactors, X] using h

/-- The actual dual tensor measurability is produced, rather than assumed. -/
theorem IsMeasurable.orthogonalTensorPair_dual {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hHξ : ξ.IsHermitian hN) (hHη : η.IsHermitian hN) :
    (ξ.orthogonalTensorPair η hN hHξ hHη).dual.IsMeasurable :=
  (hξ.orthogonalTensorPair hη hS hN hHξ hHη).dual_of_discrete_or_countable hS

end NormFamily

namespace AdelicVectorBundle

/-- The actual binary Hermitian tensor bundle, with its analytic properties
produced from the factors and the source measurability alternatives. -/
def orthogonalTensorPair (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.IsHermitian hN) (hW : W.IsHermitian hN) :
    AdelicVectorBundle S (E ⊗[K] F) :=
  ofMeasurableDominated (V.toNormFamily.orthogonalTensorPair W.toNormFamily hN hV hW)
    (V.isMeasurable.orthogonalTensorPair W.isMeasurable hS hN hV hW)
    (V.isDominated.strong_orthogonalTensorPair W.isDominated hN hV hW).isDominated hS

@[simp]
theorem orthogonalTensorPair_toNormFamily (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.IsHermitian hN) (hW : W.IsHermitian hN) :
    (V.orthogonalTensorPair W hS hN hV hW).toNormFamily =
      V.toNormFamily.orthogonalTensorPair W.toNormFamily hN hV hW := rfl

/-- The canonical tensor bundle is strongly adelic in its actual norms. -/
theorem orthogonalTensorPair_isStronglyAdelic (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.IsHermitian hN) (hW : W.IsHermitian hN) :
    (V.orthogonalTensorPair W hS hN hV hW).IsStronglyAdelic :=
  V.isDominated.strong_orthogonalTensorPair W.isDominated hN hV hW

/-- The actual binary tensor bundle has the orthogonal product inner norm. -/
theorem orthogonalTensorPair_isHermitian (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.IsHermitian hN) (hW : W.IsHermitian hN) :
    (V.orthogonalTensorPair W hS hN hV hW).IsHermitian hN :=
  NormFamily.orthogonalTensorPair_isHermitian _ _ hN hV hW

end AdelicVectorBundle

end

end ArakelovGeometry

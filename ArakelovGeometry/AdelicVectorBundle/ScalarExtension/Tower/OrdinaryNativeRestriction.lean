/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.Discrete
public import ArakelovGeometry.AdelicVectorBundle.Minima.Absolute.CompatibleTower
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.EquivalencePullback

import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Isometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Native.Degree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Compatible.DeterminantDegree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Compatible.NativeRestriction
import Mathlib.CategoryTheory.Category.Init

/-!
# Ordinary native restrictions in compatible external towers

Original common countable density or countable discrete places produce actual
direct native restrictions over an algebraically closed final field. The
genuine tower transport and restricted associator then produce ordinary bundles
on the literal iterated native subspaces and preserve canonical degrees.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic L M] [Algebra.IsAlgebraic K M]
  [IsAlgClosed M] {S : AdelicStructure K}
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

omit [Algebra K L] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic L M] in
/-- Every direct native restriction is ordinary adelic under the original
common-density or countable-discrete alternatives. -/
abbrev scalarExtensionRestrictionOfScalarMeasurability (V : AdelicVectorBundle S)
    [hreg : S.ScalarExtensionMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (B : Submodule M (M ⊗[K] V)) : AdelicVectorBundle (S.algebraicExtension M) where
  carrier := B
  toNormFamily := (V.toNormFamily.scalarExtension (L := M)).restrict B
  toIsAdelic := {
    isMeasurable := by
      rcases hreg.condition with h | ⟨hc, hd⟩
      · exact ((V.scalarExtension (hS := h)).restrictOfNormMeasurability B
          (hS := ⟨(Or.inr (h.algebraicExtension_of_isAlgClosed (L := M)))⟩)).isMeasurable
      · let := hc
        let := hd
        exact (V.scalarExtensionRestrictionOfCountableDiscreteBase B).isMeasurable
    dual_isMeasurable := by
      rcases hreg.condition with h | ⟨hc, hd⟩
      · exact ((V.scalarExtension (hS := h)).restrictOfNormMeasurability B
          (hS := ⟨(Or.inr (h.algebraicExtension_of_isAlgClosed (L := M)))⟩)).dual_isMeasurable
      · let := hc
        let := hd
        exact (V.scalarExtensionRestrictionOfCountableDiscreteBase B).dual_isMeasurable
    isDominated := by
      exact (NormFamily.IsDominated.scalarExtension_isStronglyDominated
        V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike)).isDominated.restrict B
  }

@[simp]
theorem scalarExtensionRestrictionOfScalarMeasurability_toNormFamily
    (V : AdelicVectorBundle S)
    [hreg : S.ScalarExtensionMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (B : Submodule M (M ⊗[K] V)) :
    (V.scalarExtensionRestrictionOfScalarMeasurability B).toNormFamily =
      (V.toNormFamily.scalarExtension (L := M)).restrict B := rfl

/-- The determinant of the actual direct native bundle is measurable by the
produced closure density or the accepted finite-stage discrete descent. -/
theorem scalarExtensionRestrictionOfScalarMeasurability_determinant_isMeasurable
    (V : AdelicVectorBundle S)
    [hreg : S.ScalarExtensionMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (B : Submodule M (M ⊗[K] V)) :
    (V.scalarExtensionRestrictionOfScalarMeasurability
      B).toNormFamily.determinant.IsMeasurable :=
    by
  rcases hreg.condition with h | ⟨hc, hd⟩
  · exact NormFamily.IsMeasurable.determinant_of_discrete_or_countable
      (V.scalarExtensionRestrictionOfScalarMeasurability (hreg := ⟨(Or.inl h)⟩)
        B).isMeasurable
      (hS := ⟨(Or.inr (h.algebraicExtension_of_isAlgClosed (L := M)))⟩)
  · let := hc
    let := hd
    exact V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
      B

/-- Transport a direct native restriction to the iterated scalar-extension space. -/
abbrev ordinaryNativeTowerBundle (V : AdelicVectorBundle S)
    [hreg : S.ScalarExtensionMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] V))) :
    AdelicVectorBundle ((S.algebraicExtension L).algebraicExtension M) :=
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M V
  let R := V.scalarExtensionRestrictionOfScalarMeasurability (A.map c.toLinearMap)
  (R.compatibleTowerPullback (L := L)).pullbackEquiv (c.submoduleMap A)

/-- The transported bundle has the literal iterated restriction norm family. -/
theorem ordinaryNativeTowerBundle_normFamily (V : AdelicVectorBundle S)
    [S.ScalarExtensionMeasurabilityHypotheses]
    [S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] V))) :
    (ordinaryNativeTowerBundle V A).toNormFamily =
      ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A :=
  V.toNormFamily.scalarExtension_compatibleTower_restrict_pullback A

/-- A genuine ordinary bundle on each literal iterated native subspace,
produced from original common density or countable discrete places. -/
abbrev nativeCompatibleTowerRestrictionOfScalarMeasurability (V : AdelicVectorBundle S)
    [hreg : S.ScalarExtensionMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] V))) :
    AdelicVectorBundle ((S.algebraicExtension L).algebraicExtension M) where
  carrier := A
  toNormFamily := ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A
  toIsAdelic := {
    isMeasurable := by
      rw [← ordinaryNativeTowerBundle_normFamily V A]
      exact (ordinaryNativeTowerBundle V A).isMeasurable
    dual_isMeasurable := by
      rw [← ordinaryNativeTowerBundle_normFamily V A]
      exact (ordinaryNativeTowerBundle V A).dual_isMeasurable
    isDominated := by
      rw [← ordinaryNativeTowerBundle_normFamily V A]
      exact (ordinaryNativeTowerBundle V A).isDominated
  }

@[simp]
theorem nativeCompatibleTowerRestrictionOfScalarMeasurability_toNormFamily
    (V : AdelicVectorBundle S)
    [hreg : S.ScalarExtensionMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] V))) :
    (V.nativeCompatibleTowerRestrictionOfScalarMeasurability A).toNormFamily =
      ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A := rfl

/-- Direct determinant measurability, actual tower transport and equivalence
pullback produce the determinant measurability of the literal iterated bundle. -/
theorem nativeCompatibleTowerRestrictionOfScalarMeasurability_determinant_isMeasurable
    (V : AdelicVectorBundle S)
    [hreg : S.ScalarExtensionMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] V))) :
    (V.nativeCompatibleTowerRestrictionOfScalarMeasurability
      A).toNormFamily.determinant.IsMeasurable := by
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M V
  let R := V.scalarExtensionRestrictionOfScalarMeasurability (A.map c.toLinearMap)
  let T := R.compatibleTowerPullback (L := L)
  have hdet : T.toNormFamily.determinant.IsMeasurable :=
    R.toNormFamily.determinant_isMeasurable_compatibleTowerPullback
      (hdet := (V.scalarExtensionRestrictionOfScalarMeasurability_determinant_isMeasurable
        (A.map c.toLinearMap)))
  change NormFamily.IsMeasurable
    (((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A).determinant
  rw [← ordinaryNativeTowerBundle_normFamily V A]
  exact T.pullbackEquiv_determinant_isMeasurable (c.submoduleMap A) (hdet := hdet)

variable [S.IsProper]

/-- Canonical measurable-determinant degree of the actual iterated native
restriction, with determinant measurability and normalization produced. -/
def nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability (V : AdelicVectorBundle S)
    [hreg : S.ScalarExtensionMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] V))) : ℝ :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension L) M
  (V.nativeCompatibleTowerRestrictionOfScalarMeasurability A).degreeOfMeasurableDeterminant
    (hdet :=
      (V.nativeCompatibleTowerRestrictionOfScalarMeasurability_determinant_isMeasurable A))
    (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M)
      (hS := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩))⟩)

/-- Every actual nested native degree equals the canonical direct native
degree of its associator image. Intermediate place regularity is unnecessary. -/
theorem nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability_eq_direct
    (V : AdelicVectorBundle S)
    [hreg : S.ScalarExtensionMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] V))) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M V
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    V.nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability A =
      AdelicVectorBundle.degreeOfMeasurableDeterminant
        (V.scalarExtensionRestrictionOfScalarMeasurability (A.map c.toLinearMap))
        (hdet :=
          (V.scalarExtensionRestrictionOfScalarMeasurability_determinant_isMeasurable
          (A.map c.toLinearMap)))
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension L) M
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M V
  let R := V.scalarExtensionRestrictionOfScalarMeasurability (A.map c.toLinearMap)
  let T := R.compatibleTowerPullback (L := L)
  let W := V.nativeCompatibleTowerRestrictionOfScalarMeasurability A
  let hdet :=
    V.nativeCompatibleTowerRestrictionOfScalarMeasurability_determinant_isMeasurable A
  let hNT := AdelicStructure.isRCLikeNormedField_algebraicExtension
    (S := S.algebraicExtension L) (L := M)
    (hS := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩)
  have he : ∀ x z, T.toNormFamily.norm x
      ((c.submoduleMap A).toLinearMap.baseChange
        (((S.algebraicExtension L).algebraicExtension M).ϕ x).Completion z) =
        W.toNormFamily.norm x z := by
    intro x z
    exact DFunLike.congr_fun (congrArg (fun η => η.norm x)
      (V.toNormFamily.scalarExtension_compatibleTower_restrict_pullback A)) z
  have hd := W.degreeOfMeasurableDeterminant_eq_of_completed_isometry
    T (c.submoduleMap A) (hdet := hdet) (hN := ⟨hNT⟩) he
  change W.degreeOfMeasurableDeterminant (hdet := hdet) (hN := ⟨hNT⟩) = _
  rw [hd]
  exact R.degreeOfMeasurableDeterminant_compatibleTowerPullback
    (hdet := (V.scalarExtensionRestrictionOfScalarMeasurability_determinant_isMeasurable
      (A.map c.toLinearMap)))

/-- On the common-density branch, the actual nested degree is the usual
degree of the same actual direct native scalar restriction. -/
theorem nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability_eq_common_degree
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] V))) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M V
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    V.nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability (hreg := ⟨(Or.inl
      hcount)⟩) A =
      ((V.scalarExtension (L := M)).restrictOfNormMeasurability (A.map c.toLinearMap)
        (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := M)))⟩)).degree
        (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := M)))⟩)
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M))⟩) := by
  rw [V.nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability_eq_direct]
  rfl

/-- On the countable-discrete branch the actual nested degree is exactly
the existing native direct restriction degree used by absolute invariants. -/
theorem
    nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability_eq_countable_discrete_degree
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] V))) :
    V.nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability
      (hreg := ⟨(Or.inr ⟨inferInstance, inferInstance⟩)⟩) A =
      V.nativeRestrictionDegreeOfCountableDiscreteBase
        (A.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M V).toLinearMap) := by
  rw [V.nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability_eq_direct]
  rfl

/-- The genuine rank-zero native restriction retains its empty-determinant
degree zero through the external tower. -/
theorem
    nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability_eq_zero_of_finrank_eq_zero
    (V : AdelicVectorBundle S)
    [hreg : S.ScalarExtensionMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] V))) (hr : Module.finrank M A = 0) :
    V.nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability A = 0 := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M V
  have hB : Module.finrank M (A.map c.toLinearMap) = 0 := by
    rw [← (c.submoduleMap A).finrank_eq, hr]
  rcases hreg.condition with h | ⟨hc, hd⟩
  · rw [V.nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability_eq_common_degree]
    exact ((V.scalarExtension (L := M) (hS := h)).restrictOfNormMeasurability (A.map c.toLinearMap)
      (hS := ⟨(Or.inr (h.algebraicExtension_of_isAlgClosed
          (L := M)))⟩)).degree_eq_zero_of_finrank_eq_zero
        hB
  · let := hc
    let := hd
    rw
      [V.nativeCompatibleTowerRestrictionDegreeOfScalarMeasurability_eq_countable_discrete_degree]
    exact V.nativeRestrictionDegreeOfCountableDiscreteBase_eq_zero (A.map c.toLinearMap) hB

end ArakelovGeometry.AdelicVectorBundle

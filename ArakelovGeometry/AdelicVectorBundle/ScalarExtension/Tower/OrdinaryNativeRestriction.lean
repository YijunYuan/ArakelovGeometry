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
def scalarExtensionRestrictionOfOrdinaryBase (V : AdelicVectorBundle S E)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized]
    (B : Submodule M (M ⊗[K] E)) : AdelicVectorBundle (S.algebraicExtension M) B where
  toNormFamily := (V.toNormFamily.scalarExtension (L := M)).restrict B
  isMeasurable := by
    rcases hreg.condition with h | ⟨hc, hd⟩
    · exact ((V.scalarExtension (hS := h)).restrictOfMeasurableBase B
        (hS := ⟨(Or.inr (h.algebraicExtension_of_isAlgClosed (L := M)))⟩)).isMeasurable
    · let := hc
      let := hd
      exact (V.scalarExtensionRestrictionOfCountableDiscreteBase B).isMeasurable
  dual_isMeasurable := by
    rcases hreg.condition with h | ⟨hc, hd⟩
    · exact ((V.scalarExtension (hS := h)).restrictOfMeasurableBase B
        (hS := ⟨(Or.inr (h.algebraicExtension_of_isAlgClosed (L := M)))⟩)).dual_isMeasurable
    · let := hc
      let := hd
      exact (V.scalarExtensionRestrictionOfCountableDiscreteBase B).dual_isMeasurable
  isDominated := by
    exact (NormFamily.IsDominated.scalarExtension_isStronglyDominated
      V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike)).isDominated.restrict B

@[simp]
theorem scalarExtensionRestrictionOfOrdinaryBase_toNormFamily (V : AdelicVectorBundle S E)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized]
    (B : Submodule M (M ⊗[K] E)) :
    (V.scalarExtensionRestrictionOfOrdinaryBase B).toNormFamily =
      (V.toNormFamily.scalarExtension (L := M)).restrict B := rfl

/-- The determinant of the actual direct native bundle is measurable by the
produced closure density or the accepted finite-stage discrete descent. -/
theorem scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable
    (V : AdelicVectorBundle S E)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized]
    (B : Submodule M (M ⊗[K] E)) :
    (V.scalarExtensionRestrictionOfOrdinaryBase B).toNormFamily.determinant.IsMeasurable :=
    by
  rcases hreg.condition with h | ⟨hc, hd⟩
  · exact NormFamily.IsMeasurable.determinant_of_discrete_or_countable
      (V.scalarExtensionRestrictionOfOrdinaryBase (hreg := ⟨(Or.inl h)⟩) B).isMeasurable
      (hS := ⟨(Or.inr (h.algebraicExtension_of_isAlgClosed (L := M)))⟩)
  · let := hc
    let := hd
    exact V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
      B

/-- Transport a direct native restriction to the iterated scalar-extension space. -/
def ordinaryNativeTowerBundle (V : AdelicVectorBundle S E)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    AdelicVectorBundle ((S.algebraicExtension L).algebraicExtension M) A :=
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  let R := V.scalarExtensionRestrictionOfOrdinaryBase (A.map c.toLinearMap)
  (R.compatibleTowerPullback (L := L)).pullbackEquiv (c.submoduleMap A)

/-- The transported bundle has the literal iterated restriction norm family. -/
theorem ordinaryNativeTowerBundle_normFamily (V : AdelicVectorBundle S E)
    [S.HasOrdinaryBase]
    [S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    (ordinaryNativeTowerBundle V A).toNormFamily =
      ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A :=
  V.toNormFamily.scalarExtension_compatibleTower_restrict_pullback A

/-- A genuine ordinary bundle on each literal iterated native subspace,
produced from original common density or countable discrete places. -/
def nativeCompatibleTowerRestrictionOfOrdinaryBase (V : AdelicVectorBundle S E)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    AdelicVectorBundle ((S.algebraicExtension L).algebraicExtension M) A where
  toNormFamily := ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A
  isMeasurable := by
    rw [← ordinaryNativeTowerBundle_normFamily V A]
    exact (ordinaryNativeTowerBundle V A).isMeasurable
  dual_isMeasurable := by
    rw [← ordinaryNativeTowerBundle_normFamily V A]
    exact (ordinaryNativeTowerBundle V A).dual_isMeasurable
  isDominated := by
    rw [← ordinaryNativeTowerBundle_normFamily V A]
    exact (ordinaryNativeTowerBundle V A).isDominated

@[simp]
theorem nativeCompatibleTowerRestrictionOfOrdinaryBase_toNormFamily (V : AdelicVectorBundle S E)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    (V.nativeCompatibleTowerRestrictionOfOrdinaryBase A).toNormFamily =
      ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A := rfl

/-- Direct determinant measurability, actual tower transport and equivalence
pullback produce the determinant measurability of the literal iterated bundle. -/
theorem nativeCompatibleTowerRestrictionOfOrdinaryBase_determinant_isMeasurable
    (V : AdelicVectorBundle S E)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    (V.nativeCompatibleTowerRestrictionOfOrdinaryBase
      A).toNormFamily.determinant.IsMeasurable := by
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  let R := V.scalarExtensionRestrictionOfOrdinaryBase (A.map c.toLinearMap)
  let T := R.compatibleTowerPullback (L := L)
  have hdet : T.toNormFamily.determinant.IsMeasurable :=
    R.toNormFamily.determinant_isMeasurable_compatibleTowerPullback
      (hdet := (V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable
        (A.map c.toLinearMap)))
  change NormFamily.IsMeasurable
    (((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A).determinant
  rw [← ordinaryNativeTowerBundle_normFamily V A]
  exact T.pullbackEquiv_determinant_isMeasurable (c.submoduleMap A) (hdet := hdet)

variable [S.IsProper]

/-- Canonical measurable-determinant degree of the actual iterated native
restriction, with determinant measurability and normalization produced. -/
def nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase (V : AdelicVectorBundle S E)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) : ℝ :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension L) M
  (V.nativeCompatibleTowerRestrictionOfOrdinaryBase A).degreeOfMeasurableDeterminant
    (hdet := (V.nativeCompatibleTowerRestrictionOfOrdinaryBase_determinant_isMeasurable A))
    (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M)
      (hS := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩))⟩)

/-- Every actual nested native degree equals the canonical direct native
degree of its associator image. Intermediate place regularity is unnecessary. -/
theorem nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_direct
    (V : AdelicVectorBundle S E)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase A =
      AdelicVectorBundle.degreeOfMeasurableDeterminant
        (V.scalarExtensionRestrictionOfOrdinaryBase (A.map c.toLinearMap))
        (hdet := (V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable
          (A.map c.toLinearMap)))
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension L) M
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  let R := V.scalarExtensionRestrictionOfOrdinaryBase (A.map c.toLinearMap)
  let T := R.compatibleTowerPullback (L := L)
  let W := V.nativeCompatibleTowerRestrictionOfOrdinaryBase A
  let hdet := V.nativeCompatibleTowerRestrictionOfOrdinaryBase_determinant_isMeasurable A
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
    (hdet := (V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable
      (A.map c.toLinearMap)))

/-- On the common-density branch, the actual nested degree is the usual
degree of the same actual direct native scalar restriction. -/
theorem nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_common_degree
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase (hreg := ⟨(Or.inl hcount)⟩) A =
      ((V.scalarExtension (L := M)).restrictOfMeasurableBase (A.map c.toLinearMap)
        (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := M)))⟩)).degree
        (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := M)))⟩)
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M))⟩) := by
  rw [V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_direct]
  rfl

/-- On the countable-discrete branch the actual nested degree is exactly
the existing native direct restriction degree used by absolute invariants. -/
theorem nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_countable_discrete_degree
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] (V : AdelicVectorBundle S E)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase
      (hreg := ⟨(Or.inr ⟨inferInstance, inferInstance⟩)⟩) A =
      V.nativeRestrictionDegreeOfCountableDiscreteBase
        (A.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap) := by
  rw [V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_direct]
  rfl

/-- The genuine rank-zero native restriction retains its empty-determinant
degree zero through the external tower. -/
theorem nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_zero_of_finrank_eq_zero
    (V : AdelicVectorBundle S E)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) (hr : Module.finrank M A = 0) :
    V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase A = 0 := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  have hB : Module.finrank M (A.map c.toLinearMap) = 0 := by
    rw [← (c.submoduleMap A).finrank_eq, hr]
  rcases hreg.condition with h | ⟨hc, hd⟩
  · rw [V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_common_degree]
    exact ((V.scalarExtension (L := M) (hS := h)).restrictOfMeasurableBase (A.map c.toLinearMap)
      (hS := ⟨(Or.inr (h.algebraicExtension_of_isAlgClosed
          (L := M)))⟩)).degree_eq_zero_of_finrank_eq_zero
        hB
  · let := hc
    let := hd
    rw [V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_countable_discrete_degree]
    exact V.nativeRestrictionDegreeOfCountableDiscreteBase_eq_zero (A.map c.toLinearMap) hB

end ArakelovGeometry.AdelicVectorBundle

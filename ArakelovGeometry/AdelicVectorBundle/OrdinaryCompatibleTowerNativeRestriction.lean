/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.EquivalencePullback
import ArakelovGeometry.AdelicVectorBundle.CompatibleTowerNativeRestriction
import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariantsDiscrete
import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants

/-!
# Ordinary native restrictions in compatible external towers

Original common countable density or countable discrete places produce actual
direct native restrictions over an algebraically closed final field. The
genuine tower transport and restricted associator then produce ordinary bundles
on the literal iterated native subspaces and preserve canonical degrees.
-/

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
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (B : Submodule M (M ⊗[K] E)) : AdelicVectorBundle (S.algebraicExtension M) B where
  toNormFamily := (V.toNormFamily.scalarExtension (L := M)).restrict B
  isMeasurable := by
    rcases hreg with h | ⟨hc, hd⟩
    · exact ((V.scalarExtension h hN).restrictOfMeasurableBase B
        (Or.inr (h.algebraicExtension_of_isAlgClosed (L := M)))).isMeasurable
    · let := hc
      let := hd
      exact (V.scalarExtensionRestrictionOfCountableDiscreteBase hN B).isMeasurable
  dual_isMeasurable := by
    rcases hreg with h | ⟨hc, hd⟩
    · exact ((V.scalarExtension h hN).restrictOfMeasurableBase B
        (Or.inr (h.algebraicExtension_of_isAlgClosed (L := M)))).dual_isMeasurable
    · let := hc
      let := hd
      exact (V.scalarExtensionRestrictionOfCountableDiscreteBase hN B).dual_isMeasurable
  isDominated := (NormFamily.IsDominated.scalarExtension_isStronglyDominated
    V.toNormFamily V.isDominated (S.v_Ωinf_lt_top_of_isRCLike hN)).isDominated.restrict B

@[simp]
theorem scalarExtensionRestrictionOfOrdinaryBase_toNormFamily (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (B : Submodule M (M ⊗[K] E)) :
    (V.scalarExtensionRestrictionOfOrdinaryBase hreg hN B).toNormFamily =
      (V.toNormFamily.scalarExtension (L := M)).restrict B := rfl

/-- The determinant of the actual direct native bundle is measurable by the
produced closure density or the accepted finite-stage discrete descent. -/
theorem scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (B : Submodule M (M ⊗[K] E)) :
    (V.scalarExtensionRestrictionOfOrdinaryBase hreg hN B).toNormFamily.determinant.IsMeasurable :=
    by
  rcases hreg with h | ⟨hc, hd⟩
  · exact NormFamily.IsMeasurable.determinant_of_discrete_or_countable
      (V.scalarExtensionRestrictionOfOrdinaryBase (Or.inl h) hN B).isMeasurable
      (Or.inr (h.algebraicExtension_of_isAlgClosed (L := M)))
  · let := hc
    let := hd
    exact V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
      hN B

private def ordinaryNativeTowerBundle (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    AdelicVectorBundle ((S.algebraicExtension L).algebraicExtension M) A :=
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  let R := V.scalarExtensionRestrictionOfOrdinaryBase hreg hN (A.map c.toLinearMap)
  (R.compatibleTowerPullback (L := L)).pullbackEquiv (c.submoduleMap A)

private theorem ordinaryNativeTowerBundle_normFamily (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    (ordinaryNativeTowerBundle V hreg hN A).toNormFamily =
      ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A :=
  V.toNormFamily.scalarExtension_compatibleTower_restrict_pullback A

/-- A genuine ordinary bundle on each literal iterated native subspace,
produced from original common density or countable discrete places. -/
def nativeCompatibleTowerRestrictionOfOrdinaryBase (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    AdelicVectorBundle ((S.algebraicExtension L).algebraicExtension M) A where
  toNormFamily := ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A
  isMeasurable := by
    rw [← ordinaryNativeTowerBundle_normFamily V hreg hN A]
    exact (ordinaryNativeTowerBundle V hreg hN A).isMeasurable
  dual_isMeasurable := by
    rw [← ordinaryNativeTowerBundle_normFamily V hreg hN A]
    exact (ordinaryNativeTowerBundle V hreg hN A).dual_isMeasurable
  isDominated := by
    rw [← ordinaryNativeTowerBundle_normFamily V hreg hN A]
    exact (ordinaryNativeTowerBundle V hreg hN A).isDominated

@[simp]
theorem nativeCompatibleTowerRestrictionOfOrdinaryBase_toNormFamily (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    (V.nativeCompatibleTowerRestrictionOfOrdinaryBase hreg hN A).toNormFamily =
      ((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A := rfl

/-- Direct determinant measurability, actual tower transport and equivalence
pullback produce the determinant measurability of the literal iterated bundle. -/
theorem nativeCompatibleTowerRestrictionOfOrdinaryBase_determinant_isMeasurable
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    (V.nativeCompatibleTowerRestrictionOfOrdinaryBase
      hreg hN A).toNormFamily.determinant.IsMeasurable := by
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  let R := V.scalarExtensionRestrictionOfOrdinaryBase hreg hN (A.map c.toLinearMap)
  let T := R.compatibleTowerPullback (L := L)
  have hdet : T.toNormFamily.determinant.IsMeasurable :=
    R.toNormFamily.determinant_isMeasurable_compatibleTowerPullback
      (V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable
        hreg hN (A.map c.toLinearMap))
  change NormFamily.IsMeasurable
    (((V.toNormFamily.scalarExtension (L := L)).scalarExtension (L := M)).restrict A).determinant
  rw [← ordinaryNativeTowerBundle_normFamily V hreg hN A]
  exact T.pullbackEquiv_determinant_isMeasurable (c.submoduleMap A) hdet

variable [S.IsProper]

/-- Canonical measurable-determinant degree of the actual iterated native
restriction, with determinant measurability and normalization produced. -/
def nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) : ℝ :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension L) M
  (V.nativeCompatibleTowerRestrictionOfOrdinaryBase hreg hN A).degreeOfMeasurableDeterminant
    (V.nativeCompatibleTowerRestrictionOfOrdinaryBase_determinant_isMeasurable hreg hN A)
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN))

/-- Every actual nested native degree equals the canonical direct native
degree of its associator image. Intermediate place regularity is unnecessary. -/
theorem nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_direct
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase hreg hN A =
      AdelicVectorBundle.degreeOfMeasurableDeterminant
        (V.scalarExtensionRestrictionOfOrdinaryBase hreg hN (A.map c.toLinearMap))
        (V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable
          hreg hN (A.map c.toLinearMap))
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension L) M
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  let R := V.scalarExtensionRestrictionOfOrdinaryBase hreg hN (A.map c.toLinearMap)
  let T := R.compatibleTowerPullback (L := L)
  let W := V.nativeCompatibleTowerRestrictionOfOrdinaryBase hreg hN A
  let hdet := V.nativeCompatibleTowerRestrictionOfOrdinaryBase_determinant_isMeasurable hreg hN A
  let hNT := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M)
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)
  have he : ∀ x z, T.toNormFamily.norm x
      ((c.submoduleMap A).toLinearMap.baseChange
        (((S.algebraicExtension L).algebraicExtension M).ϕ x).Completion z) =
        W.toNormFamily.norm x z := by
    intro x z
    exact DFunLike.congr_fun (congrArg (fun η => η.norm x)
      (V.toNormFamily.scalarExtension_compatibleTower_restrict_pullback A)) z
  have hd := W.degreeOfMeasurableDeterminant_eq_of_completed_isometry
    T (c.submoduleMap A) hdet hNT he
  change W.degreeOfMeasurableDeterminant hdet hNT = _
  rw [hd]
  exact R.degreeOfMeasurableDeterminant_compatibleTowerPullback
    (V.scalarExtensionRestrictionOfOrdinaryBase_determinant_isMeasurable
      hreg hN (A.map c.toLinearMap)) hN

/-- On the common-density branch, the actual nested degree is the usual
degree of the same actual direct native scalar restriction. -/
theorem nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_common_degree
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase (Or.inl hcount) hN A =
      ((V.scalarExtension (L := M) hcount hN).restrictOfMeasurableBase (A.map c.toLinearMap)
        (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := M)))).degree
        (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := M)))
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M) hN) := by
  rw [V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_direct]
  rfl

/-- On the countable-discrete branch the actual nested degree is exactly
the existing native direct restriction degree used by absolute invariants. -/
theorem nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_countable_discrete_degree
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) :
    V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase
      (Or.inr ⟨inferInstance, inferInstance⟩) hN A =
      V.nativeRestrictionDegreeOfCountableDiscreteBase hN
        (A.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E).toLinearMap) := by
  rw [V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_direct]
  rfl

/-- The genuine rank-zero native restriction retains its empty-determinant
degree zero through the external tower. -/
theorem nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_zero_of_finrank_eq_zero
    (V : AdelicVectorBundle S E)
    (hreg : S.HasCommonCountableDenseSubfield ∨
      (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule M (M ⊗[L] (L ⊗[K] E))) (hr : Module.finrank M A = 0) :
    V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase hreg hN A = 0 := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  have hB : Module.finrank M (A.map c.toLinearMap) = 0 := by
    rw [← (c.submoduleMap A).finrank_eq, hr]
  rcases hreg with h | ⟨hc, hd⟩
  · rw [V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_common_degree]
    exact ((V.scalarExtension (L := M) h hN).restrictOfMeasurableBase (A.map c.toLinearMap)
      (Or.inr (h.algebraicExtension_of_isAlgClosed (L := M)))).degree_eq_zero_of_finrank_eq_zero
        _ _ hB
  · let := hc
    let := hd
    rw [V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_countable_discrete_degree]
    exact V.nativeRestrictionDegreeOfCountableDiscreteBase_eq_zero hN (A.map c.toLinearMap) hB

end ArakelovGeometry.AdelicVectorBundle

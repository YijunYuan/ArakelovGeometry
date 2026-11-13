/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.Ordinary.Closure

import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants.Closure
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual ordinary native absolute suprema through arbitrary towers

The genuine associator reindexes all literal iterated native restrictions and
all positive-rank means. The original absolute invariants are consequently
computed on the actual nested closure norm family, with regularity supplied
only by the original base.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic L M] [Algebra.IsAlgebraic K M]
  [IsAlgClosed M] {S : AdelicStructure K} [S.IsProper]
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Every literal iterated native subspace corresponds to a direct native
subspace with the same actual degree; neither supremum needs attainment. -/
theorem iSup_nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_direct
    (V : AdelicVectorBundle S)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized] :
    (⨆ A : Submodule M (M ⊗[L] (L ⊗[K] V)),
      (V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase A : EReal)) =
    ⨆ B : Submodule M (M ⊗[K] V),
      (V.nativeRestrictionDegreeOfOrdinaryBase B : EReal) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M V
  let o := Submodule.orderIsoMapComap c
  have hd (A : Submodule M (M ⊗[L] (L ⊗[K] V))) :
      V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase A =
        V.nativeRestrictionDegreeOfOrdinaryBase (A.map c.toLinearMap) :=
    V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_direct A
  apply le_antisymm
  · apply iSup_le
    intro A
    rw [hd A]
    exact le_iSup (fun B : Submodule M (M ⊗[K] V) =>
      (V.nativeRestrictionDegreeOfOrdinaryBase B : EReal)) _
  · apply iSup_le
    intro B
    obtain ⟨A, rfl⟩ := o.surjective B
    change (V.nativeRestrictionDegreeOfOrdinaryBase
      (A.map c.toLinearMap) : EReal) ≤ _
    rw [← hd A]
    exact le_iSup (fun A : Submodule M (M ⊗[L] (L ⊗[K] V)) =>
      (V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase A : EReal)) A

/-- The genuine associator preserves every positive native rank and mean,
including the source's empty maximal-slope index set. -/
theorem iSup_nativeCompatibleTowerMeanOfOrdinaryBase_eq_direct
    (V : AdelicVectorBundle S)
    [hreg : S.HasOrdinaryBase]
    [hN : S.IsArchimedeanNormalized] :
    (⨆ A : {A : Submodule M (M ⊗[L] (L ⊗[K] V)) // 0 < Module.finrank M A},
      (V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase A.val /
        (Module.finrank M A.val : ℝ) : EReal)) =
    ⨆ B : {B : Submodule M (M ⊗[K] V) // 0 < Module.finrank M B},
      (V.nativeRestrictionDegreeOfOrdinaryBase B.val /
        (Module.finrank M B.val : ℝ) : EReal) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M V
  let o := Submodule.orderIsoMapComap c
  have hd (A : Submodule M (M ⊗[L] (L ⊗[K] V))) :
      V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase A =
        V.nativeRestrictionDegreeOfOrdinaryBase (A.map c.toLinearMap) :=
    V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_direct A
  apply le_antisymm
  · apply iSup_le
    intro A
    have hr := (c.submoduleMap A.val).finrank_eq
    have hB : 0 < Module.finrank M (A.val.map c.toLinearMap) := hr ▸ A.property
    rw [hd A.val, hr]
    exact le_iSup (fun B : {B : Submodule M (M ⊗[K] V) // 0 < Module.finrank M B} =>
      (V.nativeRestrictionDegreeOfOrdinaryBase B.val /
        (Module.finrank M B.val : ℝ) : EReal)) ⟨A.val.map c.toLinearMap, hB⟩
  · apply iSup_le
    intro B
    let A := o.symm B.val
    have ho : A.map c.toLinearMap = B.val := o.apply_symm_apply B.val
    have hr : Module.finrank M A = Module.finrank M B.val := by
      have hr := (c.submoduleMap A).finrank_eq
      rw [ho] at hr
      exact hr
    have hA : 0 < Module.finrank M A := hr.symm ▸ B.property
    have hdegree := hd A
    rw [ho] at hdegree
    exact (le_of_eq (by rw [← hdegree, ← hr])).trans
      (le_iSup (fun A : {A : Submodule M (M ⊗[L] (L ⊗[K] V)) // 0 < Module.finrank M A} =>
        (V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase A.val /
          (Module.finrank M A.val : ℝ) : EReal)) ⟨A, hA⟩)

/-- The existing common-density absolute positive degree is the canonical
degree supremum of every literal nested native restriction. -/
theorem absolutePositiveDegree_eq_iSup_compatibleTower_of_common_density
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    V.absolutePositiveDegree =
      ⨆ A : Submodule M (M ⊗[L] (L ⊗[K] V)),
        (V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase
            (hreg := ⟨(Or.inl hcount)⟩) A : EReal) :=
    by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  rw [V.absolutePositiveDegree_eq_scalarExtension_of_isAlgClosed (L := M)]
  change (⨆ B : Submodule M (M ⊗[K] V),
    (V.nativeRestrictionDegreeOfOrdinaryBase (hreg := ⟨(Or.inl hcount)⟩) B : EReal)) = _
  exact (V.iSup_nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_direct
    (L := L) (hreg := ⟨(Or.inl hcount)⟩)).symm

/-- Every actual positive-rank nested mean computes the existing
common-density absolute maximal-slope supremum. -/
theorem absoluteMaximalSlope_eq_iSup_compatibleTower_of_common_density
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized] :
    V.absoluteMaximalSlope =
      ⨆ A : {A : Submodule M (M ⊗[L] (L ⊗[K] V)) // 0 < Module.finrank M A},
        (V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase (hreg := ⟨(Or.inl hcount)⟩) A.val /
          (Module.finrank M A.val : ℝ) : EReal) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  rw [V.absoluteMaximalSlope_eq_scalarExtension_of_isAlgClosed (L := M)]
  change (⨆ B : {B : Submodule M (M ⊗[K] V) // 0 < Module.finrank M B},
    (V.nativeRestrictionDegreeOfOrdinaryBase (hreg := ⟨(Or.inl hcount)⟩) B.val /
      (Module.finrank M B.val : ℝ) : EReal)) = _
  exact (V.iSup_nativeCompatibleTowerMeanOfOrdinaryBase_eq_direct
    (L := L) (hreg := ⟨(Or.inl hcount)⟩)).symm

/-- The original discrete absolute positive degree is evaluated on ALL actual
nested native subspaces, without intermediate or target regularity. -/
theorem absolutePositiveDegreeOfCountableDiscreteBase_eq_iSup_compatibleTower
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    V.absolutePositiveDegreeOfCountableDiscreteBase =
      ⨆ A : Submodule M (M ⊗[L] (L ⊗[K] V)),
        (V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase
          (hreg := ⟨(Or.inr ⟨inferInstance, inferInstance⟩)⟩) A : EReal) := by
  rw [V.absolutePositiveDegreeOfCountableDiscreteBase_eq_iSup_of_isAlgClosed (M := M)]
  exact (V.iSup_nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase_eq_direct
    (L := L) (hreg := ⟨(Or.inr ⟨inferInstance, inferInstance⟩)⟩)).symm

/-- The original discrete absolute maximal slope is evaluated on ALL actual
positive-rank nested means, retaining the empty-supremum convention. -/
theorem absoluteMaximalSlopeOfCountableDiscreteBase_eq_iSup_compatibleTower
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized] :
    V.absoluteMaximalSlopeOfCountableDiscreteBase =
      ⨆ A : {A : Submodule M (M ⊗[L] (L ⊗[K] V)) // 0 < Module.finrank M A},
        (V.nativeCompatibleTowerRestrictionDegreeOfOrdinaryBase
          (hreg := ⟨(Or.inr ⟨inferInstance, inferInstance⟩)⟩) A.val /
          (Module.finrank M A.val : ℝ) : EReal) := by
  rw [V.absoluteMaximalSlopeOfCountableDiscreteBase_eq_iSup_of_isAlgClosed (M := M)]
  exact (V.iSup_nativeCompatibleTowerMeanOfOrdinaryBase_eq_direct
    (L := L) (hreg := ⟨(Or.inr ⟨inferInstance, inferInstance⟩)⟩)).symm

end ArakelovGeometry.AdelicVectorBundle

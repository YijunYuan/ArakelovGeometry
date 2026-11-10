/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.CompatibleTowerNativeRestriction
public import ArakelovGeometry.AdelicVectorBundle.GeometricAbsoluteInvariantsClosure

/-!
# Actual geometric absolute invariants in arbitrary external towers

All literal native subspaces and their ranks are reindexed through the
canonical associator. The original absolute invariants are evaluated on
the actual nested closure curve, without intermediate regularity assumptions.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
namespace NormFamily

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic L M] [Algebra.IsAlgebraic K M]
  [IsAlgClosed M] {S : AdelicStructure K} [S.IsProper]
  [MeasurableSingletonClass S.Ω]
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Every literal iterated native subspace corresponds to a direct native
subspace with the same actual degree; neither supremum needs attainment. -/
theorem iSup_nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms_eq_direct
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    (⨆ A : Submodule M (M ⊗[L] (L ⊗[K] E)),
      (ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms hξ hpos hS A : EReal)) =
    ⨆ B : Submodule M (M ⊗[K] E),
      (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS B : EReal) := by
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  let o := Submodule.orderIsoMapComap c
  apply le_antisymm
  · apply iSup_le
    intro A
    rw [ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms_eq_direct hξ hpos hS A]
    exact le_iSup (fun B : Submodule M (M ⊗[K] E) =>
      (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS B : EReal)) _
  · apply iSup_le
    intro B
    obtain ⟨A, rfl⟩ := o.surjective B
    change (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS
      (A.map c.toLinearMap) : EReal) ≤ _
    rw [← ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms_eq_direct hξ hpos hS A]
    exact le_iSup (fun A : Submodule M (M ⊗[L] (L ⊗[K] E)) =>
      (ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms hξ hpos hS A : EReal)) A

/-- The genuine associator preserves every positive native rank and mean,
including the source's empty maximal-slope index set. -/
theorem iSup_nativeCompatibleTowerMeanOfPositiveAtoms_eq_direct
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    (⨆ A : {A : Submodule M (M ⊗[L] (L ⊗[K] E)) // 0 < Module.finrank M A},
      (ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms hξ hpos hS A.val /
        (Module.finrank M A.val : ℝ) : EReal)) =
    ⨆ B : {B : Submodule M (M ⊗[K] E) // 0 < Module.finrank M B},
      (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS B.val /
        (Module.finrank M B.val : ℝ) : EReal) := by
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M E
  let o := Submodule.orderIsoMapComap c
  apply le_antisymm
  · apply iSup_le
    intro A
    have hr := (c.submoduleMap A.val).finrank_eq
    have hB : 0 < Module.finrank M (A.val.map c.toLinearMap) := hr ▸ A.property
    rw [ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms_eq_direct hξ hpos hS A.val, hr]
    exact le_iSup (fun B : {B : Submodule M (M ⊗[K] E) // 0 < Module.finrank M B} =>
      (ξ.nativeAlgebraicRestrictionDegreeOfPositiveAtoms hξ hpos hS B.val /
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
    have hd := ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms_eq_direct hξ hpos hS A
    rw [ho] at hd
    exact (le_of_eq (by rw [← hd, ← hr])).trans
      (le_iSup (fun A : {A : Submodule M (M ⊗[L] (L ⊗[K] E)) // 0 < Module.finrank M A} =>
        (ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms hξ hpos hS A.val /
          (Module.finrank M A.val : ℝ) : EReal)) ⟨A, hA⟩)

/-- The original absolute positive degree is the canonical degree supremum
of every actual native subspace over the true iterated closure curve. -/
theorem absolutePositiveDegreeOfPositiveAtoms_eq_iSup_compatibleTower
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ξ.absolutePositiveDegreeOfPositiveAtoms hξ hpos hS =
      ⨆ A : Submodule M (M ⊗[L] (L ⊗[K] E)),
        (ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms hξ hpos hS A : EReal) := by
  rw [ξ.absolutePositiveDegreeOfPositiveAtoms_eq_iSup_of_isAlgClosed (L := M) hξ hpos hS]
  exact (ξ.iSup_nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms_eq_direct
    (L := L) hξ hpos hS).symm

/-- The original absolute maximal slope is the supremum of all actual
positive-rank means over the genuine iterated closure curve. -/
theorem absoluteMaximalSlopeOfPositiveAtoms_eq_iSup_compatibleTower
    (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ξ.absoluteMaximalSlopeOfPositiveAtoms hξ hpos hS =
      ⨆ A : {A : Submodule M (M ⊗[L] (L ⊗[K] E)) // 0 < Module.finrank M A},
        (ξ.nativeCompatibleTowerRestrictionDegreeOfPositiveAtoms hξ hpos hS A.val /
          (Module.finrank M A.val : ℝ) : EReal) := by
  rw [ξ.absoluteMaximalSlopeOfPositiveAtoms_eq_iSup_of_isAlgClosed (L := M) hξ hpos hS]
  exact (ξ.iSup_nativeCompatibleTowerMeanOfPositiveAtoms_eq_direct (L := L) hξ hpos hS).symm

end NormFamily
end ArakelovGeometry

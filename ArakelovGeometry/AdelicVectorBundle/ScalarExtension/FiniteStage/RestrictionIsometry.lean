/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerPlace
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Basic

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Archimedean
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.ComplexDescent
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Restriction isometries over a complexifying finite stage

Complexifying finite-stage descent identifies restrictions of a scalar-extended
norm family with extensions of its finite-stage restrictions on every completed
vector. The construction requires algebraic scalar extension and the stated
Archimedean normalization; it does not impose countability or discreteness on
the place space.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u w wE
variable {K : Type u} [Field K] {S : AdelicStructure K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

private theorem scalarExtension_restrict_subtype_norm_eq (ξ : NormFamily S E)
    [hξ : ξ.IsUltrametricAtFinitePlaces]
    [hN : S.IsArchimedeanNormalized]
    (hi : ∃ a : K, a ^ 2 = -1) (A : Submodule K E)
    (x : S.ParameterSpaceExtension L) (z : x.abv.Completion ⊗[L] (L ⊗[K] A)) :
    (ξ.scalarExtension (L := L)).norm x
        ((A.subtype.baseChange L).baseChange x.abv.Completion z) =
      ((ξ.restrict A).scalarExtension (L := L)).norm x z := by
  exact ξ.scalarExtension_pullback_norm_eq_of_sqrt_neg_one (hξ := hξ) hi A.subtype
    A.subtype_injective x z

/-- A commuting subspace inclusion transports restriction norms through an algebraic tower. -/
theorem scalarExtension_restrict_tower_norm_eq
    {F : Type*} [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L]
    (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (hi : ∃ a : F, a ^ 2 = -1) (B : Submodule F (F ⊗[K] E))
    (A : Submodule L (L ⊗[K] E)) (e : L ⊗[F] B →ₗ[L] A)
    (he : A.subtype.comp e =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap.comp
        (B.subtype.baseChange L))
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (z : x.abv.Completion ⊗[L] (L ⊗[F] B)) :
    ((ξ.scalarExtension (L := L)).restrict A).norm
      (scalarExtensionTowerPlace x) (e.baseChange x.abv.Completion z) =
    (((ξ.scalarExtension (L := F)).restrict B).scalarExtension (L := L)).norm x z := by
  have hz := DFunLike.congr_fun
    (congrArg (fun f ↦ f.baseChange x.abv.Completion) he) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
  erw [(ξ.scalarExtension (L := L)).restrict_norm A (scalarExtensionTowerPlace x)]
  erw [hz]
  have hξF : (ξ.scalarExtension (L := F)).IsUltrametricAtFinitePlaces :=
    ξ.scalarExtension_isUltrametricAtFinitePlaces
  calc
    _ = ((ξ.scalarExtension (L := F)).scalarExtension (L := L)).norm x
        ((B.subtype.baseChange L).baseChange x.abv.Completion z) :=
      (ξ.scalarExtension_trans x
        ((B.subtype.baseChange L).baseChange x.abv.Completion z)).symm
    _ = _ := scalarExtension_restrict_subtype_norm_eq (ξ.scalarExtension (L := F))
      hi B x z

/-- Actual finite-stage restriction and direct native restriction agree on
all completed vectors through the canonical subspace tensor equivalence.
No original finite-place ultrametric hypothesis is needed after the first extension. -/
theorem scalarExtension_restrict_finiteStage_norm_eq (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (B : Submodule F (F ⊗[K] E))
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (z : x.abv.Completion ⊗[L] (L ⊗[F] B)) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let e := (Submodule.toBaseChange.toLinearEquiv L B).trans (c.submoduleMap (B.baseChange L))
    ((ξ.scalarExtension (L := L)).restrict ((B.baseChange L).map c.toLinearMap)).norm
      (scalarExtensionTowerPlace x) (e.toLinearMap.baseChange x.abv.Completion z) =
    (((ξ.scalarExtension (L := F)).restrict B).scalarExtension (L := L)).norm x z :=
  scalarExtension_restrict_tower_norm_eq ξ hi B _ _ rfl x z

/-- Every finite actual target subspace family admits one produced complexifying
field and actual finite-stage native restrictions whose extended norms are
isometric to the prescribed native target restrictions on every completed vector. -/
theorem exists_complexFiniteStage_restriction_isometries [IsAlgClosed L]
    (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    {ι : Type*} [Finite ι] (A : ι → Submodule L (L ⊗[K] E)) :
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ B : ι → Submodule F (F ⊗[K] E),
        (∀ i, Submodule.map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
          ((B i).baseChange L) = A i) ∧
        (∀ i, Module.finrank F (B i) = Module.finrank L (A i)) ∧
        ∀ i, ∃ e : (L ⊗[F] B i) ≃ₗ[L] A i,
          ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
            (z : x.abv.Completion ⊗[L] (L ⊗[F] B i)),
            ((ξ.scalarExtension (L := L)).restrict (A i)).norm
              (scalarExtensionTowerPlace x) (e.toLinearMap.baseChange x.abv.Completion z) =
            (((ξ.scalarExtension (L := F)).restrict (B i)).scalarExtension (L := L)).norm
              x z := by
  obtain ⟨F, hi, B, hB, hr, _⟩ := exists_complexFiniteStage_subspaces A
  refine ⟨F, hi, B, hB, hr, ?_⟩
  intro i
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let e₀ := (Submodule.toBaseChange.toLinearEquiv L (B i)).trans
    (c.submoduleMap ((B i).baseChange L))
  let e := e₀.trans (LinearEquiv.ofEq _ _ (hB i))
  refine ⟨e, ?_⟩
  intro x z
  have hc : (A i).subtype.comp e.toLinearMap =
      (((B i).baseChange L).map c.toLinearMap).subtype.comp e₀.toLinearMap := by
    rfl
  have hz := DFunLike.congr_fun
    (congrArg (fun f => f.baseChange x.abv.Completion) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
  exact (congrArg ((ξ.scalarExtension (L := L)).norm (scalarExtensionTowerPlace x)) hz).trans
    (ξ.scalarExtension_restrict_finiteStage_norm_eq F hi (B i) x z)

end NormFamily
end ArakelovGeometry

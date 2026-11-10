/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AlgebraicGeometry.CompletedFibre.Sections
import ArakelovGeometry.AlgebraicGeometry.BaseChange.AffineSectionTensor
import ArakelovGeometry.AlgebraicGeometry.CompletedFibre.BaseChange
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Actual section values under completed line-fibre tensor base change

The canonical geometric fibre isomorphism sends the value of a pulled-back
section to the literal tensor of its original value with coefficient one.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ChangeOfRings

noncomputable section

namespace ArakelovGeometry.ValuedPoint

universe u

variable {W X Y Z : Scheme.{u}}

theorem pullbackSection_square_inv (a : W ⟶ X) (b : X ⟶ Z) (c : W ⟶ Y) (d : Y ⟶ Z)
    (h : a ≫ b = c ≫ d) (M : Z.Modules) (s : Γ(M, ⊤)) :
    let e := (Scheme.Modules.pullbackComp a b).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M ≪≫
      ((Scheme.Modules.pullbackComp c d).app M).symm
    e.inv.app ⊤ (pullbackSection c _ (pullbackSection d M s)) =
      pullbackSection a _ (pullbackSection b M s) := by
  intro e
  have he := congrArg (e.inv.app ⊤) (pullbackSection_square a b c d h M s)
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app ⊤) e.hom_inv_id)
    (pullbackSection a _ (pullbackSection b M s))
  exact he.symm.trans hc

/-- Tensor values of sections in a commuting square whose upper map is affine. -/
theorem affineSection_square {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (b : Spec R ⟶ Z) (c : Spec S ⟶ Y) (d : Y ⟶ Z)
    (h : Spec.map φ ≫ b = c ≫ d) (M : Z.Modules)
    [((Scheme.Modules.pullback b).obj M).IsQuasicoherent] (s : Γ(M, ⊤)) :
    let e := (Scheme.Modules.pullbackComp (Spec.map φ) b).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M ≪≫
      ((Scheme.Modules.pullbackComp c d).app M).symm
    ((moduleSpecΓFunctor (R := S)).mapIso e.symm ≪≫
      affinePullbackSectionsIso φ ((Scheme.Modules.pullback b).obj M)).hom
        (pullbackSection c _ (pullbackSection d M s)) =
      (1 : S) ⊗ₜ[R, φ.hom] (pullbackSection b M s) := by
  have hi := pullbackSection_square_inv (Spec.map φ) b c d h M s
  have ht := congrArg (affinePullbackSectionsIso φ ((Scheme.Modules.pullback b).obj M)).hom hi
  exact ht.trans (affinePullbackSectionsIso_apply_unit φ
    ((Scheme.Modules.pullback b).obj M) (pullbackSection b M s))

/-- The same compatibility, expressed by the unit of scalar extension. -/
theorem affineSection_square_unit {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (b : Spec R ⟶ Z) (c : Spec S ⟶ Y) (d : Y ⟶ Z)
    (h : Spec.map φ ≫ b = c ≫ d) (M : Z.Modules)
    [((Scheme.Modules.pullback b).obj M).IsQuasicoherent] (s : Γ(M, ⊤)) :
    let e := (Scheme.Modules.pullbackComp (Spec.map φ) b).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M ≪≫
      ((Scheme.Modules.pullbackComp c d).app M).symm
    ((moduleSpecΓFunctor (R := S)).mapIso e.symm ≪≫
      affinePullbackSectionsIso φ ((Scheme.Modules.pullback b).obj M)).hom
        (pullbackSection c _ (pullbackSection d M s)) =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
        ((moduleSpecΓFunctor (R := R)).obj ((Scheme.Modules.pullback b).obj M))
        (pullbackSection b M s) := by
  exact affineSection_square φ b c d h M s

/-- The canonical completed line-fibre isomorphism sends the actual pulled-back
section value to the literal scalar-extension tensor of its original value. -/
theorem completedFibreBaseChangeOfFrameIso_section (f : X ⟶ Y) (M : Y.Modules)
    (x : ValuedPoint X) (U : Y.Opens) (hx : f x.point ∈ U)
    (frame : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) (s : Γ(M, ⊤)) :
    let R := CommRingCat.of (x.map f).CompletedResidueField
    let S := CommRingCat.of x.CompletedResidueField
    let φ : R ⟶ S := CommRingCat.ofHom (completedResidueMap f x)
    let b : Spec R ⟶ Y := (x.map f).completedPoint
    let c : Spec S ⟶ X := x.completedPoint
    let _ : ((Scheme.Modules.pullback b).obj M).IsQuasicoherent :=
      completedPointPullback_isQuasicoherent_of_frame M (x.map f) U hx frame
    let e := (Scheme.Modules.pullbackComp (Spec.map φ) b).app M ≪≫
      (Scheme.Modules.pullbackCongr (completedPoint_naturality f x)).app M ≪≫
      ((Scheme.Modules.pullbackComp c f).app M).symm
    ((moduleSpecΓFunctor (R := S)).mapIso e.symm ≪≫
      affinePullbackSectionsIso φ ((Scheme.Modules.pullback b).obj M)).hom
        (pullbackSection c _ (pullbackSection f M s)) =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
        ((moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pullback b).obj M))
        (pullbackSection b M s) := by
  intro R S φ b c hN
  have h := @affineSection_square_unit X Y R S φ b c f
    (completedPoint_naturality f x) M hN s
  exact h

end ArakelovGeometry.ValuedPoint

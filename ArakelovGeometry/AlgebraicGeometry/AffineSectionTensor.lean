/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AlgebraicGeometry.AffineModuleBaseChange

/-!
# The canonical section map under affine tensor base change

The affine sheaf base-change isomorphism is the one determined by the
pullback and scalar-extension adjunctions. Its compatibility with their
units identifies actual pulled-back sections with the tensors `1 ⊗ s`.
-/

open AlgebraicGeometry CategoryTheory
open scoped ChangeOfRings

noncomputable section

namespace ArakelovGeometry

universe u

variable {R S : CommRingCat.{u}}

/-- The affine tilde base-change isomorphism respects the two adjunction units. -/
theorem affinePullbackTildeIso_unit (φ : R ⟶ S) (N : ModuleCat R) :
    (tilde.adjunction (R := R)).unit.app N ≫
        (moduleSpecΓFunctor (R := R)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde N)) ≫
        (affinePushforwardSectionsIso φ).hom.app
          ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde N)) ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((moduleSpecΓFunctor (R := S)).map ((affinePullbackTildeIso φ).hom.app N)) =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app N ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj N)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
        (affinePushforwardSectionsIso φ))
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))) N
  simp only [Adjunction.ofNatIsoRight_unit,
    Adjunction.comp_unit_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.comp_map, Category.assoc] at h
  exact h

/-- The inverse affine quasi-coherent identification acts on sections as the
unit of the associated-sheaf adjunction. -/
theorem moduleSpecΓ_map_fromTildeΓ_inv (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (moduleSpecΓFunctor (R := R)).map (asIso M.fromTildeΓ).inv =
      (tilde.toTildeΓNatIso.app (moduleSpecΓFunctor.obj M)).hom := by
  apply (cancel_mono ((moduleSpecΓFunctor (R := R)).map M.fromTildeΓ)).mp
  calc
    _ = (moduleSpecΓFunctor (R := R)).map
        ((asIso M.fromTildeΓ).inv ≫ (asIso M.fromTildeΓ).hom) :=
      ((moduleSpecΓFunctor (R := R)).map_comp _ _).symm
    _ = 𝟙 _ := (congrArg ((moduleSpecΓFunctor (R := R)).map)
      (asIso M.fromTildeΓ).inv_hom_id).trans ((moduleSpecΓFunctor (R := R)).map_id _)
    _ = _ := (tilde.adjunction (R := R)).right_triangle_components M |>.symm

/-- The actual affine section isomorphism identifies the sheaf-pullback unit
with the extension-of-scalars unit. -/
theorem affinePullbackSectionsIso_hom (φ : R ⟶ S) (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    (affinePullbackSectionsIso φ M).hom =
      (moduleSpecΓFunctor (R := S)).map
        ((Scheme.Modules.pullback (Spec.map φ)).map (asIso M.fromTildeΓ).inv) ≫
      (moduleSpecΓFunctor (R := S)).map
        ((affinePullbackTildeIso φ).hom.app (moduleSpecΓFunctor.obj M)) ≫
      (tilde.toTildeΓNatIso.app
        ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M))).inv := by
  change (moduleSpecΓFunctor (R := S)).map (_ ≫ _) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  rfl

theorem affinePullbackSectionsIso_unit (φ : R ⟶ S) (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    (moduleSpecΓFunctor (R := R)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
      (affinePushforwardSectionsIso φ).hom.app
        ((Scheme.Modules.pullback (Spec.map φ)).obj M) ≫
      (ModuleCat.restrictScalars φ.hom).map (affinePullbackSectionsIso φ M).hom =
        (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (moduleSpecΓFunctor.obj M) := by
  let N := (moduleSpecΓFunctor (R := R)).obj M
  let j := (asIso M.fromTildeΓ).inv
  have hn := congrArg ((moduleSpecΓFunctor (R := R)).map)
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality j)
  simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hn
  have hp := (affinePushforwardSectionsIso φ).hom.naturality
    ((Scheme.Modules.pullback (Spec.map φ)).map j)
  simp only [Functor.comp_map] at hp
  apply (cancel_mono ((ModuleCat.restrictScalars φ.hom).map
    (tilde.toTildeΓNatIso.app ((ModuleCat.extendScalars φ.hom).obj N)).hom)).mp
  rw [affinePullbackSectionsIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  slice_lhs 2 3 => erw [← hp]
  slice_lhs 1 2 => erw [← hn]
  have hj : (moduleSpecΓFunctor (R := R)).map j = (tilde.toTildeΓNatIso.app N).hom :=
    moduleSpecΓ_map_fromTildeΓ_inv M
  rw [hj]
  have ht := affinePullbackTildeIso_unit φ N
  simp only [← Category.assoc] at ht
  exact ht

/-- Under the canonical affine base-change isomorphism an actual pulled-back
section is the literal pure tensor with coefficient one. -/
theorem affinePullbackSectionsIso_apply_unit (φ : R ⟶ S) (M : (Spec R).Modules)
    [M.IsQuasicoherent] (s : (moduleSpecΓFunctor (R := R)).obj M) :
    (affinePullbackSectionsIso φ M).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ s) =
      (1 : S) ⊗ₜ[R, φ.hom] s := by
  have h := ConcreteCategory.congr_hom (affinePullbackSectionsIso_unit φ M) s
  exact h

end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AlgebraicGeometry.CompletedLineFibre

/-!
# Completed line-fibre base change and evaluation of actual sections

Local frames produce quasi-coherence on the completed field, so line-fibre
base change holds without an affine hypothesis on the original scheme.
Evaluation uses the actual pullback adjunction unit and commutes with the
canonical completed-field square.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ArakelovGeometry.ValuedPoint

universe u

variable {X Y Z : Scheme.{u}}

/-- A frame produces quasi-coherence of the actual completed-point pullback. -/
theorem completedPointPullback_isQuasicoherent_of_frame (M : X.Modules)
    (x : ValuedPoint X) (U : X.Opens) (hx : x.point ∈ U)
    (e : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ((Scheme.Modules.pullback x.completedPoint).obj M).IsQuasicoherent := by
  apply (SheafOfModules.isQuasicoherent
    (Spec (CommRingCat.of x.CompletedResidueField)).ringCatSheaf).prop_of_iso
    (completedFibreSheafOfFrameIso M x U hx e).symm
  change (tilde (R := CommRingCat.of x.CompletedResidueField)
    (ModuleCat.of x.CompletedResidueField x.CompletedResidueField)).IsQuasicoherent
  infer_instance

/-- Completed line-fibre base change, without an affine hypothesis on the schemes. -/
def completedFibreBaseChangeOfFrameIso (f : X ⟶ Y) (M : Y.Modules) (x : ValuedPoint X)
    (U : Y.Opens) (hx : f x.point ∈ U)
    (e : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    completedFibre ((Scheme.Modules.pullback f).obj M) x ≅
      (ModuleCat.extendScalars (completedResidueMap f x)).obj (completedFibre M (x.map f)) := by
  let : ((Scheme.Modules.pullback (x.map f).completedPoint).obj M).IsQuasicoherent :=
    completedPointPullback_isQuasicoherent_of_frame M (x.map f) U hx e
  exact (moduleSpecΓFunctor (R := CommRingCat.of x.CompletedResidueField)).mapIso
    (completedFibreSheafPullbackIso f M x).symm ≪≫
    affinePullbackSectionsIso (CommRingCat.ofHom (completedResidueMap f x)) _

/-- Pullback of an actual global section, using the adjunction unit. -/
def pullbackSection (f : X ⟶ Y) (M : Y.Modules) :
    Γ(M, ⊤) →+ Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ |>.hom

/-- Actual section evaluation in the completed geometric fibre. -/
def completedSectionValue (M : X.Modules) (x : ValuedPoint X) :
    Γ(M, ⊤) →+ completedFibre M x :=
  pullbackSection x.completedPoint M

theorem pullbackSection_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ⊤ (pullbackSection (f ≫ g) M s) =
      pullbackSection f _ (pullbackSection g M s) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have h' := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app ⊤) h) s
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforward_map_app] at h'
  exact h'.symm

theorem pullbackSection_comp_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app ⊤
        (pullbackSection f _ (pullbackSection g M s)) = pullbackSection (f ≫ g) M s := by
  rw [← pullbackSection_comp]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.app ⊤) ((Scheme.Modules.pullbackComp f g).app M).inv_hom_id) _

theorem pullbackSection_congr {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app ⊤ (pullbackSection f M s) =
      pullbackSection g M s := by
  subst h
  rfl

end ArakelovGeometry.ValuedPoint

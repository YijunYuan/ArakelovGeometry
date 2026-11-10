/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Affine pullback and residue-field fibres of actual module sheaves

Pullback along a morphism of affine schemes corresponds to extension of scalars
for the associated sheaves. This supplies the affine input to geometric fibre
base change, directly in `Scheme.Modules`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ArakelovGeometry

universe u

variable {R S : CommRingCat.{u}}

/-- Global sections of the actual affine pushforward are the original
global sections with scalars restricted along the affine ring map. -/
def affinePushforwardSectionsIso (φ : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (Opposite.op ⊤))

/-- Pulling back an associated module sheaf along an affine morphism
is extension of scalars of the original module. -/
def affinePullbackTildeIso (φ : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  (((tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
      (affinePushforwardSectionsIso φ)).leftAdjointUniq
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S)))

/-- Global sections of the actual pullback of a quasi-coherent sheaf on an
affine scheme are the scalar extension of its original global sections. -/
def affinePullbackSectionsIso (φ : R ⟶ S) (M : (Spec R).Modules) [M.IsQuasicoherent] :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) ≅
      (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) :=
  moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ).symm ≪≫
      (affinePullbackTildeIso φ).app (moduleSpecΓFunctor.obj M)) ≪≫
    (tilde.toTildeΓNatIso.app _).symm

/-- The actual module fibre is the global-section module of the sheaf
pulled back along the canonical residue-field point. -/
def residueFibre {X : Scheme.{u}} (M : X.Modules) (x : X) : ModuleCat (X.residueField x) :=
  moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj M)

/-- The fibre of an affine quasi-coherent sheaf is its original section module
tensored with the actual residue field through the canonical point map. -/
def affineResidueFibreIso (M : (Spec R).Modules) [M.IsQuasicoherent] (x : Spec R) :
    residueFibre M x ≅
      (ModuleCat.extendScalars
        (Spec.preimage ((Spec R).fromSpecResidueField x)).hom).obj (moduleSpecΓFunctor.obj M) :=
  moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.pullbackCongr (Spec.map_preimage _).symm).app M) ≪≫
      affinePullbackSectionsIso _ M

/-- Formation of the actual sheaf fibre commutes with pullback, through the
canonical embedding of residue fields. This does not require quasi-coherence. -/
def residueFibreSheafPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (x : X) :
    (Scheme.Modules.pullback (Spec.map (f.residueFieldMap x))).obj
        ((Scheme.Modules.pullback (Y.fromSpecResidueField (f x))).obj M) ≅
      (Scheme.Modules.pullback (X.fromSpecResidueField x)).obj
        ((Scheme.Modules.pullback f).obj M) :=
  (Scheme.Modules.pullbackComp (Spec.map (f.residueFieldMap x))
    (Y.fromSpecResidueField (f x))).app M ≪≫
  (Scheme.Modules.pullbackCongr (f.SpecMap_residueFieldMap_fromSpecResidueField x)).app M ≪≫
  ((Scheme.Modules.pullbackComp (X.fromSpecResidueField x) f).app M).symm

end ArakelovGeometry

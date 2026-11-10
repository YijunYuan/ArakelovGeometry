/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AlgebraicGeometry.AffineModuleBaseChange

/-!
# Residue fibres of affine quasi-coherent sheaves under pullback

Affine pullback preserves quasi-coherence. Combined with the actual sheaf-fibre
square, this identifies fibres of pullback sheaves with extension of scalars
along the canonical residue-field embedding.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ArakelovGeometry

universe u

variable {R S : CommRingCat.{u}}

/-- Affine pullback preserves quasi-coherence through the actual tilde
base-change isomorphism. -/
theorem affinePullback_isQuasicoherent (φ : R ⟶ S) (M : (Spec R).Modules)
    [M.IsQuasicoherent] : ((Scheme.Modules.pullback (Spec.map φ)).obj M).IsQuasicoherent := by
  let e := (Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ).symm ≪≫
    (affinePullbackTildeIso φ).app (moduleSpecΓFunctor.obj M)
  apply (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso e.symm
  change (tilde ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M))).IsQuasicoherent
  infer_instance

/-- Pullback of an affine quasi-coherent sheaf to an actual residue field
is quasi-coherent; this is a produced property of the canonical fibre. -/
theorem residuePullback_isQuasicoherent (M : (Spec R).Modules) [M.IsQuasicoherent]
    (x : Spec R) :
    ((Scheme.Modules.pullback ((Spec R).fromSpecResidueField x)).obj M).IsQuasicoherent := by
  have h := affinePullback_isQuasicoherent
    (Spec.preimage ((Spec R).fromSpecResidueField x)) M
  simpa only [Spec.map_preimage] using h

/-- The actual residue fibre of the pulled-back affine quasi-coherent sheaf
is the extension of its original fibre along the canonical residue-field map. -/
def affineResidueFibreBaseChangeIso {X : Scheme.{u}} (f : X ⟶ Spec R)
    (M : (Spec R).Modules) [M.IsQuasicoherent] (x : X) :
    residueFibre ((Scheme.Modules.pullback f).obj M) x ≅
      (ModuleCat.extendScalars (f.residueFieldMap x).hom).obj (residueFibre M (f x)) := by
  let : ((Scheme.Modules.pullback ((Spec R).fromSpecResidueField (f x))).obj M).IsQuasicoherent :=
    residuePullback_isQuasicoherent M (f x)
  exact moduleSpecΓFunctor.mapIso (residueFibreSheafPullbackIso f M x).symm ≪≫
    affinePullbackSectionsIso (f.residueFieldMap x) _

end ArakelovGeometry

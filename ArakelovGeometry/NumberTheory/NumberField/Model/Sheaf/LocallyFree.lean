/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AlgebraicGeometry.LocallyFreeSheaf
public import ArakelovGeometry.NumberTheory.NumberField.Model.Sheaf.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Native local freeness of actual integral-lattice associated sheaves

Actual free principal sections are transported through canonical affine charts
and the usual tilde counit to actual free sheaf isomorphisms. Their principal
cover supplies native LocalGeneratorsData with all basis maps isomorphisms.
Only finite generation of the original integral submodule is required.
-/

@[expose] public section

open NumberField AlgebraicGeometry CategoryTheory
open scoped NumberField
noncomputable section

namespace ArakelovGeometry.NumberFieldFullLatticeSheaf

universe u

variable {K E : Type u} [Field K] [AddCommGroup E] [Module K E]

local notation "U" => fun f : 𝓞 K ↦
  (PrimeSpectrum.basicOpen f : Scheme.Opens (Spec (CommRingCat.of (𝓞 K))))

/-- Principal opens of the integer spectrum are affine. -/
theorem isAffineOpen_principalOpen (f : 𝓞 K) :
    IsAffineOpen (X := Spec (CommRingCat.of (𝓞 K))) (U f) :=
  IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (𝓞 K)) f

/-- The canonical affine chart of a principal open in the integer spectrum. -/
def principalAffineChart (f : 𝓞 K) :
    Spec (CommRingCat.of (principalSectionRing f)) ⟶ Spec (CommRingCat.of (𝓞 K)) :=
  (isAffineOpen_principalOpen f).fromSpec

/-- The principal affine chart is an open immersion. -/
instance principalAffineChart_isOpenImmersion (f : 𝓞 K) :
    IsOpenImmersion (principalAffineChart f) := by
  exact IsAffineOpen.isOpenImmersion_fromSpec (isAffineOpen_principalOpen f)

/-- The image of the principal affine chart is the corresponding basic open. -/
theorem basicOpen_eq_principalAffineChart_image_top (f : 𝓞 K) :
    U f = principalAffineChart f ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact (isAffineOpen_principalOpen f).opensRange_fromSpec.symm

/-- Actual restriction along the canonical affine chart of a principal open. -/
def principalAffineRestriction (L : Submodule (𝓞 K) E) (f : 𝓞 K) :
    (Spec (CommRingCat.of (principalSectionRing f))).Modules :=
  (associatedSheaf L).restrict (principalAffineChart f)

/-- The actual chart section-ring identification, using only canonical structure maps. -/
def principalRestrictionRingEquiv (f : 𝓞 K) :
    principalSectionRing f ≃+* principalSectionRing f :=
  ((Scheme.ΓSpecIso (CommRingCat.of (principalSectionRing f))).symm ≪≫
    (Scheme.Hom.appIso (principalAffineChart f) ⊤).symm ≪≫
      (Spec (CommRingCat.of (𝓞 K))).presheaf.mapIso
        (eqToIso (basicOpen_eq_principalAffineChart_image_top f)).op).commRingCatIsoToRingEquiv

attribute [local instance] RingHomInvPair.of_ringEquiv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The actual affine-chart global sections are semilinearly the original principal sections. -/
def principalAffineSectionsEquiv (L : Submodule (𝓞 K) E) (f : 𝓞 K) :
    LinearEquiv (principalRestrictionRingEquiv f :
      principalSectionRing f →+* principalSectionRing f)
      (σ' := ((principalRestrictionRingEquiv f).symm :
        principalSectionRing f →+* principalSectionRing f))
      ((moduleSpecΓFunctor (R := CommRingCat.of (principalSectionRing f))).obj
        (principalAffineRestriction L f)) (principalSections L f) := by
  let e : Γ(principalAffineRestriction L f, ⊤) ≅ principalSections L f :=
    (associatedSheaf L).restrictAppIso (principalAffineChart f) ⊤ ≪≫
      (associatedSheaf L).presheaf.mapIso
        (eqToIso (basicOpen_eq_principalAffineChart_image_top f)).op
  refine { __ := e.addCommGroupIsoToAddEquiv, map_smul' := ?_ }
  intro r x
  change e.hom (r • x) = _
  rw [Scheme.Modules.smul_Spec_def]
  dsimp only [e, Iso.trans_hom]
  rw [ConcreteCategory.comp_apply]
  erw [Scheme.Modules.smul_restrictAppIso_hom_apply (principalAffineChart f) (associatedSheaf L) ⊤]
  erw [Scheme.Modules.map_smul]
  rfl

/-- Actual freeness transports to native affine-chart global sections. -/
theorem free_principalAffineSections (L : Submodule (𝓞 K) E) (f : 𝓞 K)
    [Module.Free (principalSectionRing f) (principalSections L f)] :
    Module.Free (principalSectionRing f)
      ((moduleSpecΓFunctor (R := CommRingCat.of (principalSectionRing f))).obj
        (principalAffineRestriction L f)) :=
  (Module.Free.iff_of_equiv (principalAffineSectionsEquiv L f)).mpr inferInstance

attribute [local instance] free_principalAffineSections

/-- Transport a module sheaf on the principal affine chart to the corresponding open. -/
abbrev principalRestrictionFunctor (f : 𝓞 K) :=
  Scheme.Modules.restrictFunctor (isAffineOpen_principalOpen f).isoSpec.hom ⋙
    (Scheme.Modules.overEquiv (X := Spec (CommRingCat.of (𝓞 K))) (U f)).inverse

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The principal-chart transport preserves the unit sheaf. -/
def principalRestrictionUnitIso (f : 𝓞 K) :
    SheafOfModules.unit ((Spec (CommRingCat.of (𝓞 K))).ringCatSheaf.over (U f)) ≅
      (principalRestrictionFunctor f).obj
        (SheafOfModules.unit (Spec (CommRingCat.of (principalSectionRing f))).ringCatSheaf) :=
  ((U f).sheafOfModulesEquivOverInverseUnit
    (Spec (CommRingCat.of (𝓞 K))).ringCatSheaf).symm ≪≫
    (Scheme.Modules.overEquiv (X := Spec (CommRingCat.of (𝓞 K))) (U f)).inverse.mapIso
      (Scheme.Modules.restrictUnitIso (isAffineOpen_principalOpen f).isoSpec.hom).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting through the principal chart agrees with restriction to the principal open. -/
def principalChartRestrictionIso (L : Submodule (𝓞 K) E) (f : 𝓞 K) :
    (principalAffineRestriction L f).restrict (isAffineOpen_principalOpen f).isoSpec.hom ≅
      (associatedSheaf L).restrict
        (Scheme.Opens.ι (X := Spec (CommRingCat.of (𝓞 K))) (U f)) :=
  ((Scheme.Modules.restrictFunctorComp (isAffineOpen_principalOpen f).isoSpec.hom
    (principalAffineChart f)).app (associatedSheaf L)).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (isAffineOpen_principalOpen f).isoSpec_hom_fromSpec).app
      (associatedSheaf L)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The principal-chart transport recovers restriction of the original associated sheaf. -/
def principalRestrictionSheafIso (L : Submodule (𝓞 K) E) (f : 𝓞 K) :
    (principalRestrictionFunctor f).obj (principalAffineRestriction L f) ≅
      (associatedSheaf L).over (U f) := by
  let G := (Scheme.Modules.overEquiv (X := Spec (CommRingCat.of (𝓞 K))) (U f)).inverse
  exact G.mapIso (principalChartRestrictionIso L f) ≪≫
    G.mapIso ((Scheme.Modules.overFunctorEquiv (X := Spec (CommRingCat.of (𝓞 K)))
      (U f)).app (associatedSheaf L)).symm ≪≫
    ((Scheme.Modules.overEquiv (X := Spec (CommRingCat.of (𝓞 K))) (U f)).unitIso.app
      ((associatedSheaf L).over (U f))).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Free affine sections produce a free sheaf on the principal open. -/
def principalFreeSheafIso (L : Submodule (𝓞 K) E) (f : 𝓞 K)
    [Module.Free (principalSectionRing f) (principalSections L f)] :
    SheafOfModules.free
      (Module.Free.ChooseBasisIndex (principalSectionRing f)
        ((moduleSpecΓFunctor (R := CommRingCat.of (principalSectionRing f))).obj
          (principalAffineRestriction L f))) ≅
      (associatedSheaf L).over (U f) := by
  let A := principalAffineRestriction L f
  let F := principalRestrictionFunctor f
  let : Limits.PreservesColimitsOfSize.{u, u} F := inferInstance
  let : Module.Free (principalSectionRing f)
      ((moduleSpecΓFunctor (R := CommRingCat.of (principalSectionRing f))).obj A) :=
    free_principalAffineSections L f
  let : (associatedSheaf L).IsQuasicoherent :=
    inferInstanceAs (AlgebraicGeometry.tilde (R := CommRingCat.of (𝓞 K))
      (ModuleCat.of (𝓞 K) L)).IsQuasicoherent
  let : A.IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.restrictFunctor (principalAffineChart f)).obj
      (associatedSheaf L)).IsQuasicoherent
  exact SheafOfModules.mapFreeIso F _ (principalRestrictionUnitIso f) ≪≫
    F.mapIso (ArakelovGeometry.affineFreeSheafIso
      (CommRingCat.of (principalSectionRing f)) A) ≪≫ principalRestrictionSheafIso L f

variable [NumberField K]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Actual principal free neighborhoods and basis maps form native covering generator data. -/
def latticeLocalGeneratorsData (L : Submodule (𝓞 K) E) (hfg : L.FG) :
    (associatedSheaf L).LocalGeneratorsData where
  I := PrimeSpectrum (𝓞 K)
  X P := PrimeSpectrum.basicOpen (exists_free_principalSections_neighborhood L hfg P).choose
  coversTop := by
    rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
    apply eq_top_iff.mpr
    intro P _
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨P, (exists_free_principalSections_neighborhood L hfg P).choose_spec.1⟩
  generators P := by
    let f := (exists_free_principalSections_neighborhood L hfg P).choose
    let : Module.Free (principalSectionRing f) (principalSections L f) :=
      (exists_free_principalSections_neighborhood L hfg P).choose_spec.2
    let e := principalFreeSheafIso L f
    exact (SheafOfModules.free.generatingSections _).ofEpi e.hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual basis map in the chosen principal covering is an isomorphism. -/
instance latticeLocalGeneratorsData_isLocallyFreeData
    (L : Submodule (𝓞 K) E) (hfg : L.FG) :
    (latticeLocalGeneratorsData L hfg).IsLocallyFreeData where
  isIso P := by
    let f := (exists_free_principalSections_neighborhood L hfg P).choose
    let : Module.Free (principalSectionRing f) (principalSections L f) :=
      (exists_free_principalSections_neighborhood L hfg P).choose_spec.2
    change IsIso ((SheafOfModules.free.generatingSections _).ofEpi
      (principalFreeSheafIso L f).hom).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π]
    infer_instance

/-- Finite actual integral lattices have genuinely locally free usual associated sheaves. -/
theorem associatedSheaf_isLocallyFree (L : Submodule (𝓞 K) E) (hfg : L.FG) :
    (associatedSheaf L).IsLocallyFree :=
  (latticeLocalGeneratorsData L hfg).isLocallyFree

end ArakelovGeometry.NumberFieldFullLatticeSheaf

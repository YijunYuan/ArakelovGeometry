/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldFullLatticeSheaf
import ArakelovGeometry.AlgebraicGeometry.LocallyFreeSheaf

/-!
# Native local freeness of actual integral-lattice associated sheaves

Actual free principal sections are transported through canonical affine charts
and the usual tilde counit to actual free sheaf isomorphisms. Their principal
cover supplies native LocalGeneratorsData with all basis maps isomorphisms.
Only finite generation of the original integral submodule is required.
-/

open NumberField AlgebraicGeometry CategoryTheory
open scoped NumberField
noncomputable section

namespace ArakelovGeometry.NumberFieldFullLatticeSheaf

universe u

variable {K E : Type u} [Field K] [AddCommGroup E] [Module K E]

private abbrev X := Spec (CommRingCat.of (𝓞 K))
private abbrev U (f : 𝓞 K) : (X (K := K)).Opens := PrimeSpectrum.basicOpen f
private theorem affine (f : 𝓞 K) : IsAffineOpen (U f) :=
  IsAffineOpen.Spec_basicOpen (R := CommRingCat.of (𝓞 K)) f

private def chart (f : 𝓞 K) : Spec (CommRingCat.of (principalSectionRing f)) ⟶ X (K := K) :=
  (affine f).fromSpec

private instance chart_isOpenImmersion (f : 𝓞 K) : IsOpenImmersion (chart f) := by
  exact IsAffineOpen.isOpenImmersion_fromSpec (affine f)

private theorem image_chart_top (f : 𝓞 K) : U f = chart f ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact (affine f).opensRange_fromSpec.symm

/-- Actual restriction along the canonical affine chart of a principal open. -/
def principalAffineRestriction (L : Submodule (𝓞 K) E) (f : 𝓞 K) :
    (Spec (CommRingCat.of (principalSectionRing f))).Modules :=
  (associatedSheaf L).restrict (chart f)

/-- The actual chart section-ring identification, using only canonical structure maps. -/
def principalRestrictionRingEquiv (f : 𝓞 K) :
    principalSectionRing f ≃+* principalSectionRing f :=
  ((Scheme.ΓSpecIso (CommRingCat.of (principalSectionRing f))).symm ≪≫
    (Scheme.Hom.appIso (chart f) ⊤).symm ≪≫
      (X (K := K)).presheaf.mapIso (eqToIso (image_chart_top f)).op).commRingCatIsoToRingEquiv

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
    (associatedSheaf L).restrictAppIso (chart f) ⊤ ≪≫
      (associatedSheaf L).presheaf.mapIso (eqToIso (image_chart_top f)).op
  refine { __ := e.addCommGroupIsoToAddEquiv, map_smul' := ?_ }
  intro r x
  change e.hom (r • x) = _
  rw [Scheme.Modules.smul_Spec_def]
  dsimp only [e, Iso.trans_hom]
  rw [ConcreteCategory.comp_apply]
  erw [Scheme.Modules.smul_restrictAppIso_hom_apply (chart f) (associatedSheaf L) ⊤]
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

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Actual affine free sections produce a native free sheaf on the literal principal open. -/
def principalFreeSheafIso (L : Submodule (𝓞 K) E) (f : 𝓞 K)
    [Module.Free (principalSectionRing f) (principalSections L f)] :
    SheafOfModules.free
      (Module.Free.ChooseBasisIndex (principalSectionRing f)
        ((moduleSpecΓFunctor (R := CommRingCat.of (principalSectionRing f))).obj
          (principalAffineRestriction L f))) ≅ (associatedSheaf L).over (U f) := by
  let A := principalAffineRestriction L f
  let e := (affine f).isoSpec
  let G := (Scheme.Modules.overEquiv (U f)).inverse
  let F := Scheme.Modules.restrictFunctor e.hom ⋙ G
  let : Limits.PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor e.hom) :=
    inferInstance
  let : Limits.PreservesColimitsOfSize.{u, u} G := inferInstance
  let : Limits.PreservesColimitsOfSize.{u, u} F := inferInstance
  let : Module.Free (principalSectionRing f)
      ((moduleSpecΓFunctor (R := CommRingCat.of (principalSectionRing f))).obj A) :=
    free_principalAffineSections L f
  let : (associatedSheaf L).IsQuasicoherent :=
    inferInstanceAs (AlgebraicGeometry.tilde (R := CommRingCat.of (𝓞 K))
      (ModuleCat.of (𝓞 K) L)).IsQuasicoherent
  let : A.IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.restrictFunctor (chart f)).obj
      (associatedSheaf L)).IsQuasicoherent
  let η : SheafOfModules.unit ((X (K := K)).ringCatSheaf.over (U f)) ≅
      F.obj (SheafOfModules.unit (Spec (CommRingCat.of (principalSectionRing f))).ringCatSheaf) :=
    ((U f).sheafOfModulesEquivOverInverseUnit (X (K := K)).ringCatSheaf).symm ≪≫
      G.mapIso (Scheme.Modules.restrictUnitIso e.hom).symm
  let i : A.restrict e.hom ≅ (associatedSheaf L).restrict (U f).ι :=
    ((Scheme.Modules.restrictFunctorComp e.hom (chart f)).app (associatedSheaf L)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (affine f).isoSpec_hom_fromSpec).app
        (associatedSheaf L)
  let j : F.obj A ≅ (associatedSheaf L).over (U f) :=
    G.mapIso i ≪≫ G.mapIso ((Scheme.Modules.overFunctorEquiv (U f)).app
      (associatedSheaf L)).symm ≪≫
      ((Scheme.Modules.overEquiv (U f)).unitIso.app ((associatedSheaf L).over (U f))).symm
  exact SheafOfModules.mapFreeIso F _ η ≪≫
    F.mapIso (ArakelovGeometry.affineFreeSheafIso
      (CommRingCat.of (principalSectionRing f)) A) ≪≫ j

variable [NumberField K]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Actual principal free neighborhoods and basis maps form native covering generator data. -/
def latticeLocalGeneratorsData (L : Submodule (𝓞 K) E) (hfg : L.FG) :
    (associatedSheaf L).LocalGeneratorsData where
  I := PrimeSpectrum (𝓞 K)
  X P := U (exists_free_principalSections_neighborhood L hfg P).choose
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

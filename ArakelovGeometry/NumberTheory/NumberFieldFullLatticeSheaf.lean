/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldFullLatticeModel
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.RingTheory.Localization.Free

/-!
# The actual associated sheaf of an integral number-field lattice

The construction uses the usual associated sheaf of the literal integral
submodule. Prime-local free bases descend to actual principal neighborhoods.
-/

open NumberField AlgebraicGeometry CategoryTheory
open scoped NumberField TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace ArakelovGeometry.NumberFieldFullLatticeSheaf

attribute [local instance] RingHomInvPair.of_ringEquiv

open AdelicStructure ActualPrimeIndexing

universe u

variable {K E : Type u} [Field K] [NumberField K] [AddCommGroup E] [Module K E]

/-- The usual associated sheaf of the original integral submodule. -/
def associatedSheaf (L : Submodule (𝓞 K) E) : (Spec (.of (𝓞 K))).Modules :=
  AlgebraicGeometry.tilde (R := CommRingCat.of (𝓞 K)) (ModuleCat.of (𝓞 K) L)

/-- The canonical global sections equivalence of the actual associated sheaf. -/
def globalSectionsEquiv (L : Submodule (𝓞 K) E) :
    L ≃ₗ[𝓞 K] ((modulesSpecToSheaf.obj (associatedSheaf L)).presheaf.obj (.op ⊤)) :=
  (AlgebraicGeometry.tilde.isoTop (R := CommRingCat.of (𝓞 K))
    (ModuleCat.of (𝓞 K) L)).toLinearEquiv

/-- Literal sections of the usual associated sheaf on a principal open. -/
abbrev principalSections (L : Submodule (𝓞 K) E) (f : 𝓞 K) :=
  Γ(associatedSheaf L, PrimeSpectrum.basicOpen f)

/-- The original section-ring action on the literal principal-open sections. -/
abbrev principalSectionRing (f : 𝓞 K) :=
  Γ(Spec (CommRingCat.of (𝓞 K)), PrimeSpectrum.basicOpen f)

/-- The canonical integral action on the actual structure-sheaf section ring. -/
instance principalSectionRingAlgebra (f : 𝓞 K) :
    Algebra (𝓞 K) (principalSectionRing f) :=
  inferInstanceAs (Algebra (CommRingCat.of (𝓞 K))
    ((Spec.structureSheaf (CommRingCat.of (𝓞 K))).presheaf.obj
      (.op (PrimeSpectrum.basicOpen f))))

/-- The actual structure-sheaf action on the original associated-sheaf sections. -/
instance principalSectionModule (L : Submodule (𝓞 K) E) (f : 𝓞 K) :
    Module (principalSectionRing f) (principalSections L f) :=
  ((associatedSheaf L).val.obj (.op (PrimeSpectrum.basicOpen f))).isModule

/-- The canonical integral action on the actual associated-sheaf sections. -/
instance principalSectionIntegralModule (L : Submodule (𝓞 K) E) (f : 𝓞 K) :
    Module (𝓞 K) (principalSections L f) :=
  ((modulesSpecToSheaf.obj (associatedSheaf L)).presheaf.obj
    (.op (PrimeSpectrum.basicOpen f))).isModule

/-- The two canonical section actions are compatible. -/
instance principalSectionScalarTower (L : Submodule (𝓞 K) E) (f : 𝓞 K) :
    IsScalarTower (𝓞 K) (principalSectionRing f) (principalSections L f) :=
  IsScalarTower.of_compHom (𝓞 K) (principalSectionRing f) (principalSections L f)

/-- Actual affine structure-ring sections localize the original integral ring. -/
instance principalSectionRingLocalization (f : 𝓞 K) :
    IsLocalization.Away f (principalSectionRing f) :=
  StructureSheaf.IsLocalization.to_basicOpen (𝓞 K) f

/-- The two actual principal localization rings are canonically identified. -/
def principalSectionRingEquiv (f : 𝓞 K) :
    Localization.Away f ≃ₐ[𝓞 K] principalSectionRing f :=
  IsLocalization.algEquiv (.powers f) (Localization.Away f) (principalSectionRing f)

set_option backward.isDefEq.respectTransparency false in
/-- The literal associated-sheaf sections are canonically the module localization. -/
def principalSectionsEquiv (L : Submodule (𝓞 K) E) (f : 𝓞 K) :
    LinearEquiv ((principalSectionRingEquiv f).toRingEquiv :
      Localization.Away f →+* principalSectionRing f)
      (σ' := ((principalSectionRingEquiv f).symm.toRingEquiv :
        principalSectionRing f →+* Localization.Away f))
      (LocalizedModule.Away f L) (principalSections L f) := by
  let t : L →ₗ[𝓞 K] principalSections L f :=
    (AlgebraicGeometry.tilde.toOpen (R := CommRingCat.of (𝓞 K))
    (ModuleCat.of (𝓞 K) L) (PrimeSpectrum.basicOpen f)).hom
  let : IsLocalizedModule (.powers f) t :=
    .of_linearEquiv (.powers f) (StructureSheaf.toOpenₗ (𝓞 K) L
      (PrimeSpectrum.basicOpen f))
      ((AlgebraicGeometry.tilde.modulesSpecToSheafIso (R := CommRingCat.of (𝓞 K))
        (ModuleCat.of (𝓞 K) L)).app (.op (PrimeSpectrum.basicOpen f))).toLinearEquiv.symm
  let e : LocalizedModule.Away f L ≃ₗ[𝓞 K] principalSections L f :=
    IsLocalizedModule.linearEquiv (.powers f)
    (LocalizedModule.mkLinearMap (.powers f) L) t
  refine { __ := e.toAddEquiv, map_smul' := ?_ }
  intro r x
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) r
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units t s)).1
  simp [principalSectionRingEquiv, ← map_smul, ← smul_assoc]

omit [NumberField K] in
/-- Local freeness of a localization is transported to the literal section ring. -/
theorem free_principalSections (L : Submodule (𝓞 K) E) (f : 𝓞 K)
    [Module.Free (Localization.Away f) (LocalizedModule.Away f L)] :
    Module.Free (principalSectionRing f) (principalSections L f) :=
  (Module.Free.iff_of_equiv (principalSectionsEquiv L f)).mp inferInstance

/-- Each actual prime lies in a principal neighborhood where the lattice is free. -/
theorem exists_free_principal_neighborhood (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (P : PrimeSpectrum (𝓞 K)) :
    ∃ f : 𝓞 K, f ∉ P.asIdeal ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away f L) := by
  let : Module.Finite (𝓞 K) L := Module.Finite.of_fg hfg
  let := Module.finitePresentation_of_finite (𝓞 K) L
  let := NumberFieldFullLattice.free_prime_localization L hfg P.asIdeal
  obtain ⟨f, hf, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers P.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap P.asIdeal.primeCompl L) (Localization.AtPrime P.asIdeal)
  exact ⟨f, hf, hfree⟩

/-- Every prime has a neighborhood with actual free associated-sheaf sections. -/
theorem exists_free_principalSections_neighborhood (L : Submodule (𝓞 K) E)
    (hfg : L.FG) (P : PrimeSpectrum (𝓞 K)) :
    ∃ f : 𝓞 K, P ∈ PrimeSpectrum.basicOpen f ∧
      Module.Free (principalSectionRing f) (principalSections L f) := by
  obtain ⟨f, hf, hfree⟩ := exists_free_principal_neighborhood L hfg P
  let := hfree
  exact ⟨f, hf, free_principalSections L f⟩

end ArakelovGeometry.NumberFieldFullLatticeSheaf

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AlgebraicGeometry.CompletedFibre.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Local frames and completed line fibres

An actual local trivialization of a sheaf of modules gives a basis of its
completed geometric fibre. The fibre is obtained by pullback to the completed
residue field, rather than postulated as a separate vector space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ArakelovGeometry.ValuedPoint

variable {X Y : Scheme}

@[simp]
theorem completedPoint_apply (x : ValuedPoint X)
    (p : Spec (CommRingCat.of x.CompletedResidueField)) :
    x.completedPoint p = x.point :=
  X.fromSpecResidueField_apply x.point _

/-- The canonical completed-field point factors through every neighbourhood. -/
def completedPointToOpen (x : ValuedPoint X) (U : X.Opens) (hx : x.point ∈ U) :
    Spec (CommRingCat.of x.CompletedResidueField) ⟶ U :=
  IsOpenImmersion.lift U.ι x.completedPoint (by
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨x.point, hx⟩, (completedPoint_apply x p).symm⟩)

@[reassoc (attr := simp)]
theorem completedPointToOpen_fac (x : ValuedPoint X) (U : X.Opens) (hx : x.point ∈ U) :
    x.completedPointToOpen U hx ≫ U.ι = x.completedPoint :=
  IsOpenImmersion.lift_fac _ _ _

/-- Scheme pullback preserves the structure module. -/
def pullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  letI : (TopologicalSpace.Opens.map f.base).Final := ⟨fun V ↦ by
    let T : StructuredArrow V (TopologicalSpace.Opens.map f.base) :=
      StructuredArrow.mk (Y := ⊤) (homOfLE (by simp))
    apply isConnected_of_isTerminal _ (x := T)
    exact Limits.IsTerminal.ofUniqueHom
      (fun W ↦ StructuredArrow.homMk (homOfLE le_top))
      (fun _ _ ↦ StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _))⟩
  exact @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom)

/-- A local frame trivializes the actual completed-field pullback sheaf. -/
def completedFibreSheafOfFrameIso (M : X.Modules) (x : ValuedPoint X)
    (U : X.Opens) (hx : x.point ∈ U)
    (e : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (Scheme.Modules.pullback x.completedPoint).obj M ≅
      SheafOfModules.unit (Spec (CommRingCat.of x.CompletedResidueField)).ringCatSheaf :=
  ((Scheme.Modules.pullbackCongr (completedPointToOpen_fac x U hx)).app M).symm ≪≫
  ((Scheme.Modules.pullbackComp (x.completedPointToOpen U hx) U.ι).app M).symm ≪≫
  (Scheme.Modules.pullback (x.completedPointToOpen U hx)).mapIso
    (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ e) ≪≫
  pullbackUnitIso (x.completedPointToOpen U hx)

/-- The completed vector-space fibre identified by an actual local frame. -/
def completedFibreOfFrameIso (M : X.Modules) (x : ValuedPoint X)
    (U : X.Opens) (hx : x.point ∈ U)
    (e : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    completedFibre M x ≅ ModuleCat.of x.CompletedResidueField x.CompletedResidueField :=
  (moduleSpecΓFunctor (R := CommRingCat.of x.CompletedResidueField)).mapIso
    (completedFibreSheafOfFrameIso M x U hx e ≪≫ tildeSelf.symm) ≪≫
  (tilde.toTildeΓNatIso.app _).symm

/-- A local frame forces the actual completed fibre to have dimension one. -/
theorem finrank_completedFibre_of_frame (M : X.Modules) (x : ValuedPoint X)
    (U : X.Opens) (hx : x.point ∈ U)
    (e : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Module.finrank x.CompletedResidueField (completedFibre M x) = 1 := by
  exact (completedFibreOfFrameIso M x U hx e).toLinearEquiv.finrank_eq.trans
    (Module.finrank_self _)

/-- An invertible sheaf has one-dimensional completed fibres: the hypothesis
is the usual existence of local structure-module trivializations. -/
theorem finrank_completedFibre_of_locallyTrivial (M : X.Modules)
    (hM : ∀ p : X, ∃ (U : X.Opens), p ∈ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj M ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf)) (x : ValuedPoint X) :
    Module.finrank x.CompletedResidueField (completedFibre M x) = 1 := by
  obtain ⟨U, hx, ⟨e⟩⟩ := hM x.point
  exact finrank_completedFibre_of_frame M x U hx e

end ArakelovGeometry.ValuedPoint

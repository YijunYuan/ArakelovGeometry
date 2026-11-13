/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AlgebraicGeometry.CompletedFibre.Sections
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Section evaluation in the completed-field square

First prove section compatibility for an arbitrary commuting square of
actual scheme morphisms, then apply it to the canonical completed-field square.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ArakelovGeometry.ValuedPoint

variable {W X Y Z : Scheme}

/-- Section pullback respects an actual commuting square of scheme maps. -/
theorem pullbackSection_square (a : W ⟶ X) (b : X ⟶ Z) (c : W ⟶ Y) (d : Y ⟶ Z)
    (h : a ≫ b = c ≫ d) (M : Z.Modules) (s : Γ(M, ⊤)) :
    (((Scheme.Modules.pullbackComp a b).app M ≪≫
        (Scheme.Modules.pullbackCongr h).app M ≪≫
        ((Scheme.Modules.pullbackComp c d).app M).symm).hom).app ⊤
      (pullbackSection a _ (pullbackSection b M s)) =
        pullbackSection c _ (pullbackSection d M s) := by
  have h₁ := pullbackSection_comp_hom a b M s
  have h₂ := pullbackSection_congr h M s
  have h₃ := pullbackSection_comp c d M s
  have h₄ := congrArg (((Scheme.Modules.pullbackCongr h).app M).hom.app ⊤) h₁
  have h₅ := congrArg (((Scheme.Modules.pullbackComp c d).app M).inv.app ⊤)
    (h₄.trans h₂)
  exact h₅.trans h₃

/-- The value of a pulled-back section is its original completed value pulled
back through the canonical map of completed residue fields. -/
theorem completedSectionValue_baseChange (f : X ⟶ Y) (M : Y.Modules)
    (x : ValuedPoint X) (s : Γ(M, ⊤)) :
    let a := Spec.map (CommRingCat.ofHom (completedResidueMap f x))
    let b := (x.map f).completedPoint
    let c := x.completedPoint
    (((Scheme.Modules.pullbackComp a b).app M ≪≫
        (Scheme.Modules.pullbackCongr (completedPoint_naturality f x)).app M ≪≫
        ((Scheme.Modules.pullbackComp c f).app M).symm).hom).app ⊤
      (pullbackSection a _ (pullbackSection b M s)) =
        pullbackSection c _ (pullbackSection f M s) :=
  pullbackSection_square (Spec.map (CommRingCat.ofHom (completedResidueMap f x)))
    (x.map f).completedPoint x.completedPoint f (completedPoint_naturality f x) M s

end ArakelovGeometry.ValuedPoint

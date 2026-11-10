/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.GeometricDominationDescent
public import ArakelovGeometry.AlgebraicGeometry.ValuedPoint

/-!
# Surjectivity of finite base change on intrinsic valued points

Valued points over a specified absolute value are defined using the canonical
base-field map into their actual residue field. The compatible valued scheme
lift gives a preimage under finite base change, without additional hypotheses
on the scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ArakelovGeometry

universe u

namespace ValuedPoint

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The canonical map from the base field to the residue field of a point. -/
def baseHom (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    k →+* X.residueField x :=
  (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom

/-- Restrict the residue-field value to the base field. -/
def baseValue (f : X ⟶ Spec (CommRingCat.of k)) (x : ValuedPoint X) :
    AbsoluteValue k ℝ :=
  x.value.comp (baseHom f x.point).injective

theorem baseValue_ofField {H : Type u} [Field H]
    (f : X ⟶ Spec (CommRingCat.of k)) (a : Spec (CommRingCat.of H) ⟶ X)
    (w : AbsoluteValue H ℝ) :
    (ofField a w).baseValue f = w.comp (Spec.preimage (a ≫ f)).hom.injective := by
  let p := Scheme.SpecToEquivOfField H X a
  have ha : Spec.map p.2 ≫ X.fromSpecResidueField p.1 = a :=
    (Scheme.SpecToEquivOfField H X).symm_apply_apply a
  have hp : Spec.preimage (a ≫ f) =
      Spec.preimage (X.fromSpecResidueField p.1 ≫ f) ≫ p.2 := by
    rw [← ha, Category.assoc, Spec.preimage_comp, Spec.preimage_map]
  rw [hp]
  rfl

theorem baseValue_map (g : X ⟶ Y) (f : Y ⟶ Spec (CommRingCat.of k))
    (x : ValuedPoint X) :
    (x.map g).baseValue f = x.baseValue (g ≫ f) := by
  rw [← ofField_fromSpecResidueField x]
  erw [map_ofField, baseValue_ofField, baseValue_ofField, Category.assoc]

/-- Intrinsic valued points over one specified absolute value of the base. -/
abbrev Over (f : X ⟶ Spec (CommRingCat.of k)) (v : AbsoluteValue k ℝ) :=
  {x : ValuedPoint X // x.baseValue f = v}

theorem baseValue_comp_SpecMap {L : Type u} [Field L]
    (g : X ⟶ Spec (CommRingCat.of L)) (i : k →+* L) (x : ValuedPoint X) :
    x.baseValue (g ≫ Spec.map (CommRingCat.ofHom i)) =
      (x.baseValue g).comp i.injective := by
  ext a
  change x.value (baseHom (g ≫ Spec.map (CommRingCat.ofHom i)) x.point a) =
    x.value (baseHom g x.point (i a))
  rw [baseHom, ← Category.assoc, Spec.preimage_comp, Spec.preimage_map]
  rfl

/-- Projection on intrinsic valued points over the two specified base values. -/
def baseChangeMap {L : Type u} [Field L] [Algebra k L]
    (v : AbsoluteValue k ℝ) (vL : AbsoluteValue L ℝ) (hL : vL.under k = v)
    (f : X ⟶ Spec (CommRingCat.of k))
    (y : Over (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) vL) :
    Over f v :=
  ⟨y.1.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L)))), by
    rw [baseValue_map, pullback.condition, baseValue_comp_SpecMap, y.2]
    exact hL⟩

/-- Every intrinsic valued point over the complete ground field lifts to an
intrinsic valued point over the specified finite valued extension. -/
theorem exists_baseChange_lift {L : Type u} [Field L] [Algebra k L]
    [FiniteDimensional k L] (v : AbsoluteValue k ℝ) [CompleteSpace (WithAbs v)]
    (vL : AbsoluteValue L ℝ) (hL : vL.under k = v)
    (f : X ⟶ Spec (CommRingCat.of k)) (x : Over f v) :
    ∃ y : Over (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) vL,
      y.1.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) = x.1 := by
  let H := X.residueField x.1.point
  let : Field H := inferInstance
  let : Algebra k H := (baseHom f x.1.point).toAlgebra
  have hx : X.fromSpecResidueField x.1.point ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k H)) := by
    exact (Spec.map_preimage _).symm
  have hv : x.1.value.under k = v := x.2
  obtain ⟨i, w, hwH, hwL, a, ha, hb⟩ :=
    exists_valued_scheme_baseChange_lift v vL x.1.value hL hv X f
      (X.fromSpecResidueField x.1.point) hx
  refine ⟨⟨ofField a w, ?_⟩, ?_⟩
  · rw [baseValue_ofField, hb, Spec.preimage_map]
    exact hwL
  · rw [map_ofField, ha, ofField_precomp]
    change ofField (X.fromSpecResidueField x.1.point) (w.under H) = x.1
    rw [hwH, ofField_fromSpecResidueField]

/-- The actual projection on intrinsic valued points is surjective for a
finite extension of the complete valued ground field. -/
theorem baseChangeMap_surjective {L : Type u} [Field L] [Algebra k L]
    [FiniteDimensional k L] (v : AbsoluteValue k ℝ) [CompleteSpace (WithAbs v)]
    (vL : AbsoluteValue L ℝ) (hL : vL.under k = v)
    (f : X ⟶ Spec (CommRingCat.of k)) :
    Function.Surjective (baseChangeMap v vL hL f) := by
  intro x
  obtain ⟨y, hy⟩ := exists_baseChange_lift v vL hL f x
  exact ⟨y, Subtype.ext hy⟩

/-- The extended supremum of the absolute values of a global regular
function over the intrinsic valued points extending the given base value. -/
def regularSup (f : X ⟶ Spec (CommRingCat.of k)) (v : AbsoluteValue k ℝ)
    (s : Γ(X, ⊤)) : ENNReal :=
  ⨆ x : Over f v, ENNReal.ofReal (x.1.eval ⊤ trivial s)

/-- The structure-sheaf metric's extended supremum is preserved by finite
valued field base change, including unbounded functions and empty schemes. -/
theorem regularSup_baseChange {L : Type u} [Field L] [Algebra k L]
    [FiniteDimensional k L] (v : AbsoluteValue k ℝ) [CompleteSpace (WithAbs v)]
    (vL : AbsoluteValue L ℝ) (hL : vL.under k = v)
    (f : X ⟶ Spec (CommRingCat.of k)) (s : Γ(X, ⊤)) :
    regularSup (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) vL
        ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).appTop s) =
      regularSup f v s := by
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  unfold regularSup
  have heval (y : Over (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) vL) :
      y.1.eval ⊤ trivial (p.appTop s) =
        (baseChangeMap v vL hL f y).1.eval ⊤ trivial s := by
    exact (congrArg y.1.value (Scheme.Γevaluation_naturality_apply p y.1.point s)).symm
  exact Function.Surjective.iSup_congr (baseChangeMap v vL hL f)
    (baseChangeMap_surjective v vL hL f)
    (fun y ↦ congrArg ENNReal.ofReal (heval y).symm)

end ValuedPoint

end ArakelovGeometry

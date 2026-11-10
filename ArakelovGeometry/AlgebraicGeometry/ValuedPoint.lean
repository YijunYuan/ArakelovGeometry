/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.AlgebraicGeometry.ResidueField
import ArakelovGeometry.ExternalResults.AbsoluteValue

/-!
# Intrinsic valued points of schemes

A valued point consists of a scheme point and an absolute value on its actual
residue field. Scheme morphisms act by restriction along residue-field maps.
Field-valued representatives normalize to these intrinsic points.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ArakelovGeometry

universe u

/-- A point of a scheme equipped with a real-valued absolute value on its
actual residue field. -/
structure ValuedPoint (X : Scheme.{u}) where
  point : X
  value : AbsoluteValue (X.residueField point) ℝ

namespace ValuedPoint

variable {X Y Z : Scheme.{u}}

/-- Restriction along the canonical map of residue fields. -/
def map (f : X ⟶ Y) (x : ValuedPoint X) : ValuedPoint Y where
  point := f x.point
  value := x.value.pullback (f.residueFieldMap x.point).hom

@[simp]
theorem map_id (x : ValuedPoint X) : x.map (𝟙 X) = x := by
  cases x
  simp [map, AbsoluteValue.pullback]
  rfl

@[simp]
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : ValuedPoint X) :
    x.map (f ≫ g) = (x.map f).map g := by
  simp [map, Scheme.residueFieldMap_comp, AbsoluteValue.pullback]
  rfl

/-- A residue-field embedding into a valued field induces an intrinsic
valued point by restriction of the absolute value. -/
def ofResidueHom {H : Type u} [Field H]
    (x : Σ x : X, X.residueField x ⟶ CommRingCat.of H)
    (v : AbsoluteValue H ℝ) : ValuedPoint X where
  point := x.1
  value := v.pullback x.2.hom

/-- Normalize a valued field point to its actual residue field. -/
def ofField {H : Type u} [Field H] (a : Spec (CommRingCat.of H) ⟶ X)
    (v : AbsoluteValue H ℝ) : ValuedPoint X :=
  ofResidueHom (Scheme.SpecToEquivOfField H X a) v

@[simp]
theorem ofField_residueHom {H : Type u} [Field H] (x : X)
    (a : X.residueField x ⟶ CommRingCat.of H) (v : AbsoluteValue H ℝ) :
    ofField (Spec.map a ≫ X.fromSpecResidueField x) v =
      ⟨x, v.pullback a.hom⟩ := by
  change ofResidueHom
    ((Scheme.SpecToEquivOfField H X) ((Scheme.SpecToEquivOfField H X).symm ⟨x, a⟩)) v = _
  rw [Equiv.apply_symm_apply]
  rfl

@[simp]
theorem ofField_fromSpecResidueField (x : ValuedPoint X) :
    ofField (X.fromSpecResidueField x.point) x.value = x := by
  have h := ofField_residueHom x.point (𝟙 (X.residueField x.point)) x.value
  erw [Spec.map_id, Category.id_comp] at h
  exact h

@[simp]
theorem map_ofField {H : Type u} [Field H]
    (a : Spec (CommRingCat.of H) ⟶ X) (v : AbsoluteValue H ℝ) (f : X ⟶ Y) :
    (ofField a v).map f = ofField (a ≫ f) v := by
  simp [map, ofField, ofResidueHom, Scheme.SpecToEquivOfField,
    Scheme.descResidueField_stalkClosedPointTo_comp, AbsoluteValue.pullback]
  rfl

/-- Normalization is unchanged by replacing a field-valued representative
by an extension of its valued field. -/
theorem ofField_precomp {H M : Type u} [Field H] [Field M]
    (a : Spec (CommRingCat.of H) ⟶ X) (i : H →+* M)
    (w : AbsoluteValue M ℝ) :
    ofField (Spec.map (CommRingCat.ofHom i) ≫ a) w = ofField a (w.pullback i) := by
  let p := Scheme.SpecToEquivOfField H X a
  have ha : Spec.map p.2 ≫ X.fromSpecResidueField p.1 = a :=
    (Scheme.SpecToEquivOfField H X).symm_apply_apply a
  rw [← ha, ← Category.assoc, ← Spec.map_comp, ofField_residueHom, ofField_residueHom]
  rfl

/-- The value of a regular function at an intrinsic valued point. -/
def eval (x : ValuedPoint X) (U : X.Opens) (hx : x.point ∈ U) (s : Γ(X, U)) : ℝ :=
  x.value (X.evaluation U x.point hx s)

/-- Pulling back regular functions preserves their values at corresponding
intrinsic valued points. -/
theorem eval_map (f : X ⟶ Y) (x : ValuedPoint X) (U : Y.Opens)
    (hx : f x.point ∈ U) (s : Γ(Y, U)) :
    (x.map f).eval U hx s = x.eval (f ⁻¹ᵁ U) hx (f.app U s) := by
  exact congrArg x.value (Scheme.evaluation_naturality_apply f x.point hx s)

end ValuedPoint

end ArakelovGeometry

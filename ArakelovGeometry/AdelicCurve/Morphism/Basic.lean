/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Defs
import Mathlib.CategoryTheory.Category.Basic

/-!
# Morphisms of adelic curves

Chen–Moriwaki, Definition 3.7.1: a contravariant field homomorphism, a
measure-preserving map of parameter spaces compatible with the absolute values,
and a real-linear retraction of pullback on `L¹` preserving integrals.
The fibre operator is part of a morphism; no positivity or continuity is imposed.
-/

namespace ArakelovGeometry.AdelicCurve

open MeasureTheory

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

/-- A morphism of adelic curves, with all three data and all compatibilities of
Chen–Moriwaki, Definition 3.7.1. The direction of the field map is opposite to
the direction of the map on parameter spaces. -/
structure Hom (C : AdelicCurve.{u₁, v₁}) (D : AdelicCurve.{u₂, v₂}) where
  /-- The homomorphism of underlying fields. -/
  fieldMap : D.K →+* C.K
  /-- The map of parameter spaces. -/
  baseMap : C.Ω → D.Ω
  /-- The parameter map is measurable and sends the source measure to the target measure. -/
  measurePreserving : MeasurePreserving baseMap C.v D.v
  /-- Restricting a source absolute value along the field map gives the target value. -/
  absoluteValue_comp : ∀ (ω : C.Ω) (a : D.K),
    C.ϕ ω (fieldMap a) = D.ϕ (baseMap ω) a
  /-- The disintegration operator on equivalence classes of integrable real functions. -/
  fibreIntegral : Lp ℝ 1 C.v →ₗ[ℝ] Lp ℝ 1 D.v
  /-- Disintegration preserves the integral. -/
  integral_fibreIntegral : ∀ f : Lp ℝ 1 C.v,
    ∫ ω, fibreIntegral f ω ∂D.v = ∫ ω, f ω ∂C.v
  /-- Disintegration retracts the pullback of every integrable class on the target. -/
  fibreIntegral_pullback : ∀ f : Lp ℝ 1 D.v,
    fibreIntegral (Lp.compMeasurePreserving baseMap measurePreserving f) = f

namespace Hom

variable {C : AdelicCurve.{u₁, v₁}} {D : AdelicCurve.{u₂, v₂}}
  {E : AdelicCurve.{u₃, v₃}} {F : AdelicCurve.{u₄, v₄}}

/-- Equality of all three data determines a morphism. -/
@[ext]
theorem ext {f g : Hom C D} (hfield : f.fieldMap = g.fieldMap)
    (hbase : f.baseMap = g.baseMap) (hintegral : f.fibreIntegral = g.fibreIntegral) : f = g := by
  cases f
  cases g
  cases hfield
  cases hbase
  cases hintegral
  rfl

/-- The parameter map of a morphism is measurable. -/
theorem measurable_baseMap (f : Hom C D) : Measurable f.baseMap :=
  f.measurePreserving.measurable

/-- The pushforward of the source measure is the target measure. -/
theorem map_measure (f : Hom C D) : Measure.map f.baseMap C.v = D.v :=
  f.measurePreserving.map_eq

/-- Pullback along an adelic morphism, as a linear isometry of `L¹` spaces. -/
noncomputable def pullback (f : Hom C D) : Lp ℝ 1 D.v →ₗᵢ[ℝ] Lp ℝ 1 C.v :=
  Lp.compMeasurePreservingₗᵢ ℝ f.baseMap f.measurePreserving

/-- Pullback is represented by composition with the map on parameter spaces. -/
theorem coeFn_pullback (f : Hom C D) (g : Lp ℝ 1 D.v) :
    f.pullback g =ᵐ[C.v] g ∘ f.baseMap :=
  Lp.coeFn_compMeasurePreserving g f.measurePreserving

/-- A morphism retracts its pullback on `L¹`. -/
@[simp]
theorem fibreIntegral_pullback_apply (f : Hom C D) (g : Lp ℝ 1 D.v) :
    f.fibreIntegral (f.pullback g) = g :=
  f.fibreIntegral_pullback g

/-- Pullback preserves integrability. -/
theorem integrable_comp (f : Hom C D) {g : D.Ω → ℝ} (hg : Integrable g D.v) :
    Integrable (g ∘ f.baseMap) C.v :=
  f.measurePreserving.integrable_comp_of_integrable hg

/-- The function-level integral identity in Definition 3.7.1(b). -/
theorem integral_comp (f : Hom C D) {g : D.Ω → ℝ} (hg : Integrable g D.v) :
    ∫ ω, g (f.baseMap ω) ∂C.v = ∫ ω, g ω ∂D.v := by
  have hm : AEStronglyMeasurable g (Measure.map f.baseMap C.v) := by
    rw [f.map_measure]
    exact hg.aestronglyMeasurable
  simpa only [f.map_measure] using
    (integral_map f.measurable_baseMap.aemeasurable hm).symm

/-- The identity morphism. -/
noncomputable def id (C : AdelicCurve.{u₁, v₁}) : Hom C C where
  fieldMap := RingHom.id C.K
  baseMap := _root_.id
  measurePreserving := MeasurePreserving.id C.v
  absoluteValue_comp _ _ := rfl
  fibreIntegral := LinearMap.id
  integral_fibreIntegral _ := rfl
  fibreIntegral_pullback := Lp.compMeasurePreserving_id_apply

/-- Composition of adelic morphisms, in the same order as function composition.
The field maps compose contravariantly and the fibre operators covariantly. -/
noncomputable def comp (g : Hom D E) (f : Hom C D) : Hom C E where
  fieldMap := f.fieldMap.comp g.fieldMap
  baseMap := g.baseMap ∘ f.baseMap
  measurePreserving := g.measurePreserving.comp f.measurePreserving
  absoluteValue_comp ω a :=
    (f.absoluteValue_comp ω (g.fieldMap a)).trans (g.absoluteValue_comp (f.baseMap ω) a)
  fibreIntegral := g.fibreIntegral.comp f.fibreIntegral
  integral_fibreIntegral h :=
    (g.integral_fibreIntegral (f.fibreIntegral h)).trans (f.integral_fibreIntegral h)
  fibreIntegral_pullback h := by
    change g.fibreIntegral (f.fibreIntegral
      (Lp.compMeasurePreserving (g.baseMap ∘ f.baseMap)
        (g.measurePreserving.comp f.measurePreserving) h)) = h
    rw [Lp.compMeasurePreserving_comp_apply h g.measurePreserving f.measurePreserving,
      f.fibreIntegral_pullback,
      g.fibreIntegral_pullback]

@[simp]
theorem id_comp (f : Hom C D) : (id D).comp f = f := by
  apply ext <;> rfl

@[simp]
theorem comp_id (f : Hom C D) : f.comp (id C) = f := by
  apply ext <;> rfl

theorem comp_assoc (h : Hom E F) (g : Hom D E) (f : Hom C D) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply ext <;> rfl

/-- Pullback reverses composition. -/
@[simp]
theorem pullback_comp (g : Hom D E) (f : Hom C D) (h : Lp ℝ 1 E.v) :
    (g.comp f).pullback h = f.pullback (g.pullback h) :=
  Lp.compMeasurePreserving_comp_apply h g.measurePreserving f.measurePreserving

end Hom

/-- Adelic curves and the morphisms of Definition 3.7.1 form a category. -/
noncomputable instance category : CategoryTheory.Category AdelicCurve.{u₁, v₁} where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp := Hom.comp_id
  comp_id := Hom.id_comp
  assoc f g h := (Hom.comp_assoc h g f).symm

end ArakelovGeometry.AdelicCurve

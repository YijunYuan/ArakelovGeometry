/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Examples.RationalFunction.Construction
public import ArakelovGeometry.AdelicCurve.Morphism.Basic
public import ArakelovGeometry.ExternalResults.ProbabilityCollapse

/-!
# The rational-function morphism of adelic curves

Chen–Moriwaki, Example 3.7.2(3): the field inclusion `ℚ → ℚ(T)`, the map
collapsing the transcendental unit-circle component to the ordinary infinite
place of `ℚ`, and the fibre integral that averages over that component.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicCurve.RationalFunction

open MeasureTheory ProbabilityCollapse
open scoped AdelicStructure

/-- The concrete morphism of Example 3.7.2(3), from the rational-function curve
to the rational curve augmented by horizontal copies of the trivial place. -/
noncomputable def morphismToRationals :
    adelicStructure ⟶ augmentedRationalAdelicStructure where
  fieldMap := algebraMap ℚ (RatFunc ℚ)
  baseMap := collapse
  measurePreserving := measurePreserving_collapse finiteAdelicStructure.v archimedeanMeasure
  absoluteValue_comp ω a := by
    rcases ω with ω | t
    · rfl
    · exact archimedeanAbv_rat t a
  fibreIntegral := averageL1LinearMap finiteAdelicStructure.v archimedeanMeasure
  integral_fibreIntegral := integral_averageL1 finiteAdelicStructure.v archimedeanMeasure
  fibreIntegral_pullback :=
    averageL1_compMeasurePreserving finiteAdelicStructure.v archimedeanMeasure

@[simp]
theorem morphismToRationals_fieldMap (a : ℚ) :
    morphismToRationals.fieldMap a = algebraMap ℚ (RatFunc ℚ) a := rfl

@[simp]
theorem morphismToRationals_baseMap_finite (ω : finiteAdelicStructure.Ω) :
    morphismToRationals.baseMap (Sum.inl ω) = Sum.inl ω := rfl

@[simp]
theorem morphismToRationals_baseMap_archimedean (t : ArchimedeanPlace) :
    morphismToRationals.baseMap (Sum.inr t) = Sum.inr () := rfl

/-- The function-level fibre integral fixes every finite-place value and integrates the
archimedean component with respect to the source's restricted Lebesgue measure. -/
noncomputable def fibreAverage (f : adelicStructure.Ω → ℝ) :
    augmentedRationalAdelicStructure.Ω → ℝ := average archimedeanMeasure f

@[simp]
theorem fibreAverage_finite (f : adelicStructure.Ω → ℝ) (ω : finiteAdelicStructure.Ω) :
    fibreAverage f (Sum.inl ω) = f (Sum.inl ω) := rfl

@[simp]
theorem fibreAverage_infinite (f : adelicStructure.Ω → ℝ) :
    fibreAverage f (Sum.inr ()) = ∫ t, f (Sum.inr t) ∂archimedeanMeasure := rfl

theorem integrable_fibreAverage {f : adelicStructure.Ω → ℝ} (hf : Integrable f adelicStructure.v) :
    Integrable (fibreAverage f) augmentedRationalAdelicStructure.v :=
  integrable_average finiteAdelicStructure.v archimedeanMeasure hf

/-- On every integrable representative the morphism has the exact fibre formula of the source. -/
theorem morphismToRationals_fibreIntegral_toL1 {f : adelicStructure.Ω → ℝ}
    (hf : Integrable f adelicStructure.v) :
    morphismToRationals.fibreIntegral (hf.toL1 f) =
      (integrable_fibreAverage hf).toL1 (fibreAverage f) :=
  averageL1_toL1 finiteAdelicStructure.v archimedeanMeasure hf

end ArakelovGeometry.AdelicCurve.RationalFunction

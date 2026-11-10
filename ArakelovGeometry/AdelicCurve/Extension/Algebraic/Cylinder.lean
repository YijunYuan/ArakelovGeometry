/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Measure
import Mathlib.CategoryTheory.Category.Init

/-!
# Cylinder functions and their probability functional

Constants, positivity and linearity for the real cylinder integrals of
Chen–Moriwaki, §3.4.2.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.Algebraic
open MeasureTheory
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (AS : AdelicStructure K)

/-- Every constant global function descends to the ground-field stage. -/
noncomputable def DescendsToFinite.const (c : ℝ) :
    DescendsToFinite AS L (fun _ ↦ c) := ⟨FiniteIntermediateField.bot, fun _ ↦ c, rfl⟩

/-- Every constant fibre function descends to the ground-field stage. -/
noncomputable def DescendsToFiniteFiber.const (ω : AS.Ω) (c : ℝ) :
    DescendsToFiniteFiber (L := L) ω (fun _ ↦ c) :=
  ⟨FiniteIntermediateField.bot, fun _ ↦ c, rfl⟩

variable [Algebra.IsAlgebraic K L]
variable {AS} {ω : AS.Ω} {f g : BaseFiber L ω → ℝ}

/-- A real fibre cylinder is integrable for the actual fibre probability. -/
theorem DescendsToFiniteFiber.integrable (d : DescendsToFiniteFiber ω f) :
    Integrable f (fibreProbabilityMeasure AS L ω) := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K d.F.1) ω
  rw [d.eq_comp]
  apply Integrable.comp_measurable _ (measurable_projFiniteFiber AS L ω d.F)
  rw [map_fibreProbabilityMeasure_projFiniteFiber]
  exact ParameterSpaceExtension.integrable_fibre AS (separableClosure K d.F.1) ω d.g

/-- The cylinder functional is positive. -/
theorem fibreCylinderIntegral_nonneg (d : DescendsToFiniteFiber ω f) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ fibreCylinderIntegral d := by
  rw [← integral_fibreProbabilityMeasure_descend AS L d]
  exact integral_nonneg hf

/-- The cylinder functional is additive, independently of the chosen presentations. -/
theorem fibreCylinderIntegral_add (df : DescendsToFiniteFiber ω f) (dg : DescendsToFiniteFiber ω g)
    (d : DescendsToFiniteFiber ω (f + g)) :
    fibreCylinderIntegral d = fibreCylinderIntegral df + fibreCylinderIntegral dg := by
  rw [← integral_fibreProbabilityMeasure_descend AS L d,
    ← integral_fibreProbabilityMeasure_descend AS L df,
    ← integral_fibreProbabilityMeasure_descend AS L dg]
  exact integral_add df.integrable dg.integrable

/-- The cylinder functional commutes with real scalar multiplication. -/
theorem fibreCylinderIntegral_smul (c : ℝ) (df : DescendsToFiniteFiber ω f)
    (d : DescendsToFiniteFiber ω (c • f)) :
    fibreCylinderIntegral d = c * fibreCylinderIntegral df := by
  rw [← integral_fibreProbabilityMeasure_descend AS L d,
    ← integral_fibreProbabilityMeasure_descend AS L df]
  exact integral_smul c f

/-- The cylinder functional integrates each constant to that constant. -/
theorem fibreCylinderIntegral_const (c : ℝ) (d : DescendsToFiniteFiber (L := L) ω (fun _ ↦ c)) :
    fibreCylinderIntegral d = c := by
  rw [← integral_fibreProbabilityMeasure_descend AS L d]
  simp


section Global
variable {f g : ParameterSpaceExtension AS L → ℝ}

/-- Each global real cylinder is integrable on every probability fibre. -/
theorem DescendsToFinite.integrable_fibre (d : DescendsToFinite AS L f) (ω : AS.Ω) :
    Integrable (fun x : BaseFiber L ω ↦ f x.val) (fibreProbabilityMeasure AS L ω) := by
  apply DescendsToFiniteFiber.integrable (f := fun x ↦ f x.val)
    (ω := ω) ⟨d.F, fun y ↦ d.g y.val, ?_⟩
  funext x
  exact congrFun d.eq_comp x.val

/-- Remark 3.4.7: global cylinder integration is pointwise additive. -/
theorem fibreIntegral_add_of_descendsToFinite (df : DescendsToFinite AS L f)
    (dg : DescendsToFinite AS L g) :
    fibreIntegral AS L (f + g) = fibreIntegral AS L f + fibreIntegral AS L g := by
  funext ω
  exact integral_add (df.integrable_fibre ω) (dg.integrable_fibre ω)
end Global

end ArakelovGeometry.AdelicStructure.Algebraic

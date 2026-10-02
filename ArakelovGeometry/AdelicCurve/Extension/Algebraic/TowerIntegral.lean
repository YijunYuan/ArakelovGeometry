/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerBasic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Signed integration on algebraic tower fibres

Pushforward integration and kernel Fubini identify signed integration against
the actual fibre and iterated fibre measures, with the required integrability
hypothesis. These are the analytic steps for Chen–Moriwaki, Theorem 3.4.12.
-/

namespace ArakelovGeometry.AdelicStructure.Algebraic
open MeasureTheory ProbabilityTheory
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Integration against the probability on the total space is signed fibre integration. -/
theorem integral_fibreMeasure {f : (AS.algebraicExtension L).Ω → ℝ}
    (hf : Measurable f) (ω : AS.Ω) :
    ∫ x, f x ∂fibreMeasure AS L ω = fibreIntegral AS L f ω := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  exact integral_map (measurable_subtype_val_baseFiber AS L ω).aemeasurable
    hf.aestronglyMeasurable

/-- A measurable globally integrable function is integrable on almost every fibre measure. -/
theorem integrable_fibreMeasure_ae {f : (AS.algebraicExtension L).Ω → ℝ}
    (hf : Measurable f) (hi : Integrable f (AS.algebraicExtension L).v) :
    ∀ᵐ ω ∂AS.v, Integrable f (fibreMeasure AS L ω) := by
  filter_upwards [integrable_fibre_ae_of_measurable AS L hf hi] with ω hω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  exact (integrable_map_measure hf.aestronglyMeasurable
    (measurable_subtype_val_baseFiber AS L ω).aemeasurable).mpr hω

variable {L} in
/-- Signed Fubini for the iterated fibre measure, under integrability for that measure. -/
theorem integral_towerFibreMeasure (F : IntermediateField K L)
    {f : (AS.algebraicExtension L).Ω → ℝ} (hf : Measurable f) (ω : AS.Ω)
    (hi : Integrable f (towerFibreMeasure AS F ω)) :
    ∫ x, f x ∂towerFibreMeasure AS F ω =
      fibreIntegral AS F
        (fibreIntegral (AS.algebraicExtension F) L
          (fun z ↦ f (towerMeasurableEquiv AS F z))) ω := by
  let η : Kernel (AS.algebraicExtension F).Ω (AS.algebraicExtension L).Ω :=
    ⟨fun x ↦ Measure.map (towerMeasurableEquiv AS F)
      (fibreMeasure (AS.algebraicExtension F) L x), measurable_towerFibreKernel AS F⟩
  let κ := Kernel.const Unit (fibreMeasure AS F ω)
  have hcomp : (η.comp κ) () = towerFibreMeasure AS F ω := rfl
  have hi' : Integrable f ((η.comp κ) ()) := hcomp.symm ▸ hi
  have h := Kernel.integral_comp hi'
  rw [hcomp] at h
  let g : ((AS.algebraicExtension F).algebraicExtension L).Ω → ℝ :=
    fun z ↦ f (towerMeasurableEquiv AS F z)
  have hg : Measurable g := hf.comp (towerMeasurableEquiv AS F).measurable
  have hinner (x : (AS.algebraicExtension F).Ω) :
      (∫ y, f y ∂η x) = fibreIntegral (AS.algebraicExtension F) L g x := by
    exact (integral_map (towerMeasurableEquiv AS F).measurable.aemeasurable
      hf.aestronglyMeasurable).trans
      (integral_fibreMeasure (AS.algebraicExtension F) L hg x)
  have hgm : Measurable (fibreIntegral (AS.algebraicExtension F) L g) := by
    have hm := hf.stronglyMeasurable.integral_kernel (κ := η)
    simpa only [hinner] using hm.measurable
  calc
    _ = ∫ x, ∫ y, f y ∂η x ∂fibreMeasure AS F ω := h
    _ = ∫ x, fibreIntegral (AS.algebraicExtension F) L g x ∂fibreMeasure AS F ω :=
      integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = _ := integral_fibreMeasure AS F hgm ω

end ArakelovGeometry.AdelicStructure.Algebraic

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Finite.Tower

/-!
# Finite fibre probabilities and pullbacks

Every point of a finite extension fibre has positive mass. This upgrades almost
everywhere statements on such fibres to pointwise statements and gives invariance
of fibre integration under global almost everywhere equality. The projection
pushforward also gives nonnegative integration and integrability of base pullbacks.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Every subset of a finite extension fibre is measurable. -/
theorem measurableSet_extensionFiber (ω : AS.Ω) (s : Set (ExtensionFiber AS L ω)) :
    MeasurableSet s := by
  let := finite_extensionFiber AS L ω
  exact (Set.toFinite s).measurableSet

/-- Every finite fibre weight is strictly positive. -/
theorem fibreWeight_pos (ω : AS.Ω) (x : ExtensionFiber AS L ω) :
    0 < fibreWeight AS L ω x := by
  have : FiniteDimensional (x.val.ϕ.restriction K).Completion x.val.ϕ.Completion :=
    AbsoluteValue.finiteDimensional_completion x.val.ϕ K
  apply ENNReal.div_pos
  · exact_mod_cast (Module.finrank_pos
      (R := (x.val.ϕ.restriction K).Completion) (M := x.val.ϕ.Completion)).ne'
  · simp

/-- The mass of a point of the fibre is its local-degree weight. -/
theorem fibreProbabilityMeasure_singleton (ω : AS.Ω) (x : ExtensionFiber AS L ω) :
    fibreProbabilityMeasure AS L ω {x} = fibreWeight AS L ω x := by
  classical
  simp [fibreProbabilityMeasure,
    Measure.sum_apply _ (measurableSet_extensionFiber AS L ω {x}), Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_extensionFiber AS L ω {x}), Pi.single_apply, mul_ite]

/-- A property holds almost everywhere on a finite fibre exactly when it holds everywhere. -/
theorem ae_fibreProbabilityMeasure_iff (ω : AS.Ω) {p : ExtensionFiber AS L ω → Prop} :
    (∀ᵐ x ∂fibreProbabilityMeasure AS L ω, p x) ↔ ∀ x, p x := by
  let := finite_extensionFiber AS L ω
  rw [ae_iff_of_countable]
  simp only [fibreProbabilityMeasure_singleton]
  exact ⟨fun h x ↦ h x (ne_of_gt (fibreWeight_pos AS L ω x)), fun h x _ ↦ h x⟩

variable [Algebra.IsSeparable K L]

/-- A globally almost everywhere property holds at every point of almost every finite fibre. -/
theorem ae_forall_fibre_of_ae {p : ParameterSpaceExtension AS L → Prop}
    (hp : ∀ᵐ x ∂inducedMeasure AS L, p x) :
    ∀ᵐ ω ∂AS.v, ∀ x : ExtensionFiber AS L ω, p x.val := by
  filter_upwards [ae_ae_fibre_of_ae AS L hp] with ω hω
  exact (ae_fibreProbabilityMeasure_iff AS L ω).mp hω

/-- Real fibre integration respects globally almost everywhere equal functions. -/
theorem fibreIntegral_congr_ae {f g : ParameterSpaceExtension AS L → ℝ}
    (hfg : f =ᵐ[inducedMeasure AS L] g) :
    fibreIntegral AS L f =ᵐ[AS.v] fibreIntegral AS L g := by
  filter_upwards [ae_forall_fibre_of_ae AS L hfg] with ω hω
  exact integral_congr_ae (Filter.Eventually.of_forall hω)

/-- Pullback along the projection preserves nonnegative integrals. -/
theorem lintegral_comp_proj_inducedMeasure {g : AS.Ω → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g (proj x) ∂inducedMeasure AS L = ∫⁻ ω, g ω ∂AS.v := by
  rw [← lintegral_map hg (measurable_proj AS L), map_inducedMeasure_proj]

/-- Pullback along the projection preserves integrability. -/
theorem integrable_comp_proj_inducedMeasure {g : AS.Ω → ℝ} (hg : Integrable g AS.v) :
    Integrable (fun x ↦ g (proj x)) (inducedMeasure AS L) := by
  have hg' : Integrable g (Measure.map proj (inducedMeasure AS L)) := by
    simpa only [map_inducedMeasure_proj AS L] using hg
  exact hg'.comp_measurable (measurable_proj AS L)

end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The probability on a finite fibre is the finite sum of its weighted point masses. -/
theorem fibreProbabilityMeasure_eq_sum (ω : AS.Ω) [Fintype (BaseFiber (AS := AS) L ω)] :
    fibreProbabilityMeasure AS L ω =
      ∑ x : BaseFiber (AS := AS) L ω,
        ParameterSpaceExtension.fibreWeight AS (separableClosure K L) ω x • Measure.dirac x :=
  Measure.sum_fintype _

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension

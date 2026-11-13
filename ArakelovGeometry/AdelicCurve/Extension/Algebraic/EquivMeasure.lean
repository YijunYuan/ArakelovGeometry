/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Equiv
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.FiniteProjection
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual algebraic extension measure under base-field isomorphisms

The prescribed finite embedded marginals determine the transported projective
fibre probability. Disintegration then transports the actual total measure.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.Algebraic
open MeasureTheory
open scoped ENNReal
universe u wL wM
variable {K : Type u} [Field K] (S : AdelicStructure K)
  {L : Type wL} [Field L] [Algebra K L]
  {M : Type wM} [Field M] [Algebra K M]

/-- The actual field-isomorphism transport restricted to an original place fibre. -/
def algEquivFiber (σ : L ≃ₐ[K] M) (ω : S.Ω) : BaseFiber M ω → BaseFiber L ω :=
  fun x ↦ ⟨ParameterSpaceExtension.pullbackAlgEquiv S σ x.val, x.property⟩

/-- A transported finite projection is the accepted projection along the
corresponding finite field embedding, including inseparable stages. -/
theorem projFiniteFiber_algEquivFiber (σ : L ≃ₐ[K] M)
    (F : FiniteIntermediateField K L) (ω : S.Ω) (x : BaseFiber M ω) :
    projFiniteFiber F ω (algEquivFiber S σ ω x) =
      projFiniteFiberAlong S (σ.toAlgHom.comp F.1.val) ω x := by
  apply (ParameterSpaceFinExtension.fibreEquivAbsoluteValues S F ω).injective
  apply Subtype.ext
  change ParameterSpaceFinExtension.ϕ S F
      (projFinite S F (ParameterSpaceExtension.pullbackAlgEquiv S σ x.val)) =
    ParameterSpaceFinExtension.ϕ S F
      (projFiniteAlong S (σ.toAlgHom.comp F.1.val) x.val)
  have hval : ParameterSpaceFinExtension.ϕ S F
      (projFinite S F (ParameterSpaceExtension.pullbackAlgEquiv S σ x.val)) =
      (ParameterSpaceExtension.pullbackAlgEquiv S σ x.val).abv.under F :=
    ParameterSpaceFinExtension.extendAbsoluteValue_restriction F
      ((ParameterSpaceExtension.pullbackAlgEquiv S σ x.val).abv.under F)
  rw [hval, projFiniteAlong_ϕ]
  rfl

/-- The fibre transport is measurable for both actual projective fibre sigma algebras. -/
theorem measurable_algEquivFiber (σ : L ≃ₐ[K] M) (ω : S.Ω) :
    @Measurable (BaseFiber M ω) (BaseFiber L ω)
      (fibreMeasurableSpace M ω) (fibreMeasurableSpace L ω)
      (algEquivFiber S σ ω) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _ (⨆ F : FiniteIntermediateField K L, _) ≤ _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun F ↦ ?_
  rw [MeasurableSpace.comap_comp]
  have hcomp : projFiniteFiber F ω ∘ algEquivFiber S σ ω =
      projFiniteFiberAlong S (σ.toAlgHom.comp F.1.val) ω :=
    funext (projFiniteFiber_algEquivFiber S σ F ω)
  rw [hcomp]
  exact (measurable_projFiniteFiberAlong S (σ.toAlgHom.comp F.1.val) ω).comap_le

variable [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]

/-- The actual transported projective fibre probability has every prescribed marginal. -/
theorem map_fibreProbabilityMeasure_algEquivFiber (σ : L ≃ₐ[K] M) (ω : S.Ω) :
    let : MeasurableSpace (BaseFiber M ω) := fibreMeasurableSpace M ω
    let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
    Measure.map (algEquivFiber S σ ω) (fibreProbabilityMeasure S M ω) =
      fibreProbabilityMeasure S L ω := by
  let : MeasurableSpace (BaseFiber M ω) := fibreMeasurableSpace M ω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  apply eq_fibreProbabilityMeasure_of_map_projFiniteFiber S L ω
  intro F
  rw [Measure.map_map (measurable_projFiniteFiber S L ω F)
    (measurable_algEquivFiber S σ ω)]
  have hcomp : projFiniteFiber F ω ∘ algEquivFiber S σ ω =
      projFiniteFiberAlong S (σ.toAlgHom.comp F.1.val) ω :=
    funext (projFiniteFiber_algEquivFiber S σ F ω)
  rw [hcomp]
  exact map_fibreProbabilityMeasure_projFiniteFiberAlong S (σ.toAlgHom.comp F.1.val) ω

/-- Nonnegative integration on each actual fibre commutes with field transport. -/
theorem fibreLIntegral_comp_algEquiv (σ : L ≃ₐ[K] M)
    {f : ParameterSpaceExtension S L → ℝ≥0∞}
    (hf : Measurable[projectiveMeasurableSpace S L] f) :
    fibreLIntegral S M (fun x ↦ f (ParameterSpaceExtension.pullbackAlgEquiv S σ x)) =
      fibreLIntegral S L f := by
  funext ω
  let : MeasurableSpace (BaseFiber M ω) := fibreMeasurableSpace M ω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  change (∫⁻ x, f (algEquivFiber S σ ω x).val ∂fibreProbabilityMeasure S M ω) =
    ∫⁻ y, f y.val ∂fibreProbabilityMeasure S L ω
  rw [← lintegral_map (measurable_restrict_baseFiber S L hf ω)
    (measurable_algEquivFiber S σ ω), map_fibreProbabilityMeasure_algEquivFiber]

/-- The actual place equivalence pushes the total algebraic extension measure forward. -/
theorem map_measure_algEquivMeasurableEquiv (σ : L ≃ₐ[K] M) :
    Measure.map (ParameterSpaceExtension.algEquivMeasurableEquiv S σ)
      (S.algebraicExtension M).v = (S.algebraicExtension L).v := by
  let : MeasurableSpace (ParameterSpaceExtension S M) := projectiveMeasurableSpace S M
  let : MeasurableSpace (ParameterSpaceExtension S L) := projectiveMeasurableSpace S L
  change Measure.map (ParameterSpaceExtension.pullbackAlgEquiv S σ) (measure S M) =
    measure S L
  have hm : Measurable (ParameterSpaceExtension.pullbackAlgEquiv S σ) :=
    (ParameterSpaceExtension.algEquivMeasurableEquiv S σ).measurable
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm]
  have h := lintegral_measure S M (hf.comp hm)
  simp only [Function.comp_def] at h
  rw [h, fibreLIntegral_comp_algEquiv S σ hf]
  exact (lintegral_measure S L hf).symm

/-- Field isomorphisms preserve the actual algebraic extension measures. -/
theorem measurePreserving_algEquivMeasurableEquiv (σ : L ≃ₐ[K] M) :
    MeasurePreserving (ParameterSpaceExtension.algEquivMeasurableEquiv S σ)
      (S.algebraicExtension M).v (S.algebraicExtension L).v :=
  ⟨(ParameterSpaceExtension.algEquivMeasurableEquiv S σ).measurable,
    map_measure_algEquivMeasurableEquiv S σ⟩

end ArakelovGeometry.AdelicStructure.Algebraic

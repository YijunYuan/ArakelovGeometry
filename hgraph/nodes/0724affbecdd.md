---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.integral_fibreProbabilityMeasure_descend
docstring: 'Chen--Moriwaki, Proposition 3.4.6, formula (3.17): integrating a cylinder
  function

  against `P_{L,ω}` computes its finite-stage fibre integral `I_{L/K,ω}`.'
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Probability.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.integral_fibreProbabilityMeasure_descend
type: lean
updated: '2026-10-02T11:55:12'
---
theorem integral_fibreProbabilityMeasure_descend {ω : AS.Ω} {f : BaseFiber L ω → ℝ}
    (d : DescendsToFiniteFiber ω f) :
    ∫ x, f x ∂fibreProbabilityMeasure AS L ω = fibreCylinderIntegral d := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K d.F.1) ω
  calc
    _ = ∫ x, d.g (projFiniteFiber d.F ω x) ∂fibreProbabilityMeasure AS L ω :=
      integral_congr_ae (Filter.Eventually.of_forall (congrFun d.eq_comp))
    _ = ∫ y, d.g y ∂Measure.map (projFiniteFiber d.F ω)
        (fibreProbabilityMeasure AS L ω) :=
      (integral_map (measurable_projFiniteFiber AS L ω d.F).aemeasurable
        (measurable_of_countable d.g).aestronglyMeasurable).symm
    _ = _ := by rw [map_fibreProbabilityMeasure_projFiniteFiber]; rfl

end ArakelovGeometry.AdelicStructure.Algebraic

namespace ArakelovGeometry.AdelicStructure.Algebraic

open MeasureTheory

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

omit [Algebra.IsAlgebraic K L] in
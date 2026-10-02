---
author: sync
content_type: theorem
created: '2026-10-02T14:15:48'
decl: ArakelovGeometry.ProbabilityCollapse.measurePreserving_collapse
docstring: Collapsing a probability component preserves the disjoint-union measures.
file: ArakelovGeometry/ExternalResults/ProbabilityCollapse.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.ProbabilityCollapse.measurePreserving_collapse
type: lean
updated: '2026-10-02T14:15:48'
---
theorem measurePreserving_collapse (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure ν] :
    MeasurePreserving collapse (sumMeasure μ ν) (sumMeasure μ (Measure.dirac ())) := by
  refine ⟨measurable_collapse, ?_⟩
  rw [sumMeasure, Measure.map_add _ _ measurable_collapse,
    Measure.map_map measurable_collapse measurable_inl,
    Measure.map_map measurable_collapse measurable_inr]
  simp [collapse, Function.comp_def, sumMeasure, Measure.map_const,
    Measure.map_dirac' measurable_inr]
---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.integral_comp_projFinite_measure
docstring: Integration of an integrable pullback from a finite stage.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Integral.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.integral_comp_projFinite_measure
type: lean
updated: '2026-10-02T11:55:12'
---
theorem integral_comp_projFinite_measure (F : FiniteIntermediateField K L)
    {g : ParameterSpaceFinExtension AS F → ℝ}
    (hg : Integrable g (ParameterSpaceFinExtension.measure AS F)) :
    ∫ x, g (projFinite AS F x) ∂measure AS L =
      ∫ y, g y ∂ParameterSpaceFinExtension.measure AS F := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  rw [← map_measure_projFinite AS L F] at hg ⊢
  exact (integral_map (measurable_projFinite_projective AS L F).aemeasurable
    hg.aestronglyMeasurable).symm
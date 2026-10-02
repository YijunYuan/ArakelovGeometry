---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.integral_abs_fibreIntegral_le
docstring: 'Chen--Moriwaki, Proposition 3.4.9: algebraic fibre integration is an L1
  contraction.'
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Integral.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.integral_abs_fibreIntegral_le
type: lean
updated: '2026-10-02T11:55:12'
---
theorem integral_abs_fibreIntegral_le {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∫ ω, |fibreIntegral AS L f ω| ∂AS.v ≤ ∫ x, |f x| ∂measure AS L := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have habs : Integrable (fun x ↦ |f x|) (measure AS L) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  rw [integral_measure AS L habs]
  apply integral_mono
  · simpa only [Real.norm_eq_abs] using (integrable_fibreIntegral AS L hf).norm
  · exact integrable_fibreIntegral AS L habs
  · intro ω
    let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
    simpa only [fibreIntegral, Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := fibreProbabilityMeasure AS L ω)
        (fun x : BaseFiber L ω ↦ f x.val)
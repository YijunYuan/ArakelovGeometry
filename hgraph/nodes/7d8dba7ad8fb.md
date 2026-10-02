---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.measurable_log_projective
docstring: Logarithmic evaluations are measurable for the projective-limit σ-algebra.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Basic.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.measurable_log_projective
type: lean
updated: '2026-10-02T11:55:12'
---
theorem measurable_log_projective (a : L) :
    Measurable[projectiveMeasurableSpace AS L]
      (fun x : ParameterSpaceExtension AS L ↦ Real.log ((ParameterSpaceExtension.ϕ x) a)) :=
  (measurable_eval_projective AS L a).log
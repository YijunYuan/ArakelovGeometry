---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreIntegral_add
docstring: The fibre integration operator is additive (§3.3.1).
file: ArakelovGeometry/AdelicCurve/Extension/Separable/FibreIntegral.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreIntegral_add
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreIntegral_add (f g : ParameterSpaceExtension AS L → ℝ) :
    fibreIntegral AS L (f + g) = fibreIntegral AS L f + fibreIntegral AS L g := by
  funext ω
  exact integral_add (integrable_fibre AS L ω _) (integrable_fibre AS L ω _)

set_option linter.unusedSectionVars false in
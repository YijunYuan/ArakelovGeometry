---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.fibreIntegral_smul
docstring: Fibre integration commutes with multiplication by a real scalar.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Integrable.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.fibreIntegral_smul
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreIntegral_smul (c : ℝ) (f : ParameterSpaceExtension AS L → ℝ) :
    fibreIntegral AS L (c • f) = c • fibreIntegral AS L f := by
  funext ω
  exact integral_smul c _
---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreIntegral_one
docstring: 'Formula (3.3): the fibre integration operator sends the constant function
  `1` on `Ω_L`

  to the constant function `1` on `Ω_K` (§3.3.1).'
file: ArakelovGeometry/AdelicCurve/Extension/Separable/FibreIntegral.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreIntegral_one
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreIntegral_one : fibreIntegral AS L (fun _ ↦ 1) = fun _ ↦ 1 := by
  funext ω
  simp [fibreIntegral]
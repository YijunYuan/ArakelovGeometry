---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreWeight
docstring: 'The concrete fibre weight `[L_x : K_ω] / [L : K]` from (3.2).'
file: ArakelovGeometry/AdelicCurve/Extension/Separable/FibreIntegral.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreWeight
type: lean
updated: '2026-10-02T11:55:12'
---
noncomputable def fibreWeight (ω : AS.Ω) (x : ExtensionFiber AS L ω) : ℝ≥0∞ :=
  (localDegree x.1.ϕ K : ℝ≥0∞) / (Module.finrank K L : ℝ≥0∞)
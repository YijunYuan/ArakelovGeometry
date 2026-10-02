---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreLIntegral
docstring: The nonnegative version of the fibre integration operator, used in Definition
  3.3.6.
file: ArakelovGeometry/AdelicCurve/Extension/Separable/FibreIntegral.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreLIntegral
type: lean
updated: '2026-10-02T11:55:12'
---
noncomputable def fibreLIntegral (f : ParameterSpaceExtension AS L → ℝ≥0∞) : AS.Ω → ℝ≥0∞ :=
  fun ω ↦ ∫⁻ x : ExtensionFiber AS L ω, f x.1 ∂fibreProbabilityMeasure AS L ω

omit _s in
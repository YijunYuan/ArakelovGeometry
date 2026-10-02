---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.CylinderFunctions
docstring: The vector space of real-valued cylinder functions on `Ω_L`.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/CylinderContent.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.CylinderFunctions
type: lean
updated: '2026-10-02T11:55:12'
---
abbrev CylinderFunctions :=
  Σ f : ParameterSpaceExtension AS L → ℝ, DescendsToFinite AS L f

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
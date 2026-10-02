---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.fibreLIntegral_comp_projFiniteAlong
docstring: Nonnegative fibre integration commutes with a finite embedding projection.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/FiniteProjection.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.fibreLIntegral_comp_projFiniteAlong
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreLIntegral_comp_projFiniteAlong (g : ParameterSpaceFinExtension AS E → ℝ≥0∞) :
    fibreLIntegral AS L (fun x ↦ g (projFiniteAlong AS i x)) =
      ParameterSpaceFinExtension.fibreLIntegral AS E g := by
  funext ω
  exact lintegral_projFiniteFiberAlong AS i ω (fun y ↦ g y.val)
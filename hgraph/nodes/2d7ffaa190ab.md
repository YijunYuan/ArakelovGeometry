---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.measurable_projFiniteFiber
docstring: Finite-stage fibre projections are measurable for the cylinder σ-algebra.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/CylinderContent.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.measurable_projFiniteFiber
type: lean
updated: '2026-10-02T11:55:12'
---
theorem measurable_projFiniteFiber (ω : AS.Ω) (F : FiniteIntermediateField K L) :
    Measurable[fibreMeasurableSpace L ω] (projFiniteFiber F ω) :=
  Measurable.of_comap_le (le_iSup (fun F : FiniteIntermediateField K L ↦
    MeasurableSpace.comap (projFiniteFiber F ω) inferInstance) F)
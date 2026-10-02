---
author: sync
content_type: theorem
created: '2026-10-02T12:40:52'
decl: ArakelovGeometry.AdelicStructure.heightArchimedeanConstant_nonneg
file: ArakelovGeometry/AdelicCurve/Height/Polynomial.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.heightArchimedeanConstant_nonneg
type: lean
updated: '2026-10-02T12:40:52'
---
theorem heightArchimedeanConstant_nonneg : 0 ≤ AS.heightArchimedeanConstant :=
  integral_nonneg (fun ω ↦ (AS.κ_mem_Icc ω).1)
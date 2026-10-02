---
author: sync
content_type: theorem
created: '2026-10-02T12:11:38'
decl: ArakelovGeometry.AdelicStructure.affineHeight_zero
file: ArakelovGeometry/AdelicCurve/Height/Affine.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.affineHeight_zero
type: lean
updated: '2026-10-02T12:11:38'
---
@[simp] theorem affineHeight_zero : AS.affineHeight 0 = 0 := by
  simp [affineHeight_eq_integral]
---
author: sync
content_type: theorem
created: '2026-10-02T12:11:38'
decl: ArakelovGeometry.AdelicStructure.projectiveHeight_mk
file: ArakelovGeometry/AdelicCurve/Height/Basic.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.projectiveHeight_mk
type: lean
updated: '2026-10-02T12:11:38'
---
@[simp] theorem projectiveHeight_mk {a : ι → K} (ha : a ≠ 0) :
    AS.projectiveHeight (Projectivization.mk K a ha) = AS.logHeight a := rfl
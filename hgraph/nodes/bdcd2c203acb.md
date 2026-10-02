---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.ext
file: ArakelovGeometry/AdelicCurve/Extension/ParameterSpace.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.ext
type: lean
updated: '2026-10-02T11:55:12'
---
theorem ext {x y : ParameterSpaceExtension AS L} (hbase : x.base = y.base) (habv : x.abv = y.abv) :
    x = y := by
  cases x
  cases y
  simp_all
---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicCurve.functionFieldAdelicCurve
docstring: The adelic curve of the function field `k(X)` of `ℙ¹_k` (Chen–Moriwaki
  §3.2.1).
file: ArakelovGeometry/AdelicCurve/Examples/FunctionFields.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.functionFieldAdelicCurve
type: lean
updated: '2026-10-02T11:55:12'
---
noncomputable abbrev functionFieldAdelicCurve (k : Type*) [Field k] : AdelicCurve :=
  (functionFieldAdelicStructure k).toAdelicCurve
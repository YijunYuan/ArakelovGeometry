---
author: sync
content_type: theorem
created: '2026-10-02T14:15:48'
decl: ArakelovGeometry.ProbabilityCollapse.measurable_collapse
file: ArakelovGeometry/ExternalResults/ProbabilityCollapse.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.ProbabilityCollapse.measurable_collapse
type: lean
updated: '2026-10-02T14:15:48'
---
theorem measurable_collapse : Measurable (collapse (A := A) (B := B)) :=
  measurable_fun_sum measurable_inl measurable_const
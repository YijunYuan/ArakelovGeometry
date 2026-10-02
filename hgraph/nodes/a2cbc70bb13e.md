---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: MeasureTheory.Measure.ofSingletons_singleton
file: ArakelovGeometry/ExternalResults/Measure.lean
generated: lean
lean_status: lean_ok
title: MeasureTheory.Measure.ofSingletons_singleton
type: lean
updated: '2026-10-02T11:55:12'
---
theorem ofSingletons_singleton (f : X → ℝ≥0∞) (x : X) : ofSingletons f {x} = f x :=
  Measure.sum_smul_dirac_singleton

variable [Countable X]
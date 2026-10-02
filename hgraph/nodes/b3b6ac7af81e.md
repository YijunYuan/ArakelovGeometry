---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: MeasureTheory.boundedSequentialSpan_const
file: ArakelovGeometry/ExternalResults/BoundedFunctionalMonotoneClass.lean
generated: lean
lean_status: lean_ok
private: true
title: MeasureTheory.boundedSequentialSpan_const
type: lean
updated: '2026-10-02T11:55:12'
---
private theorem boundedSequentialSpan_const {C : Set (X → ℝ)} (h1 : (1 : X → ℝ) ∈ C) (a : ℝ) :
    (fun _ : X ↦ a) ∈ boundedSequentialSpan C := by
  simpa only [Pi.smul_def, Pi.one_apply, smul_eq_mul, mul_one] using
    (boundedSequentialSpan C).smul_mem a (subset_boundedSequentialSpan C h1)
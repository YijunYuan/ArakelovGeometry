---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AbsoluteValue.completionTensorMapOfEq_one_tmul
docstring: The tensor map extends the canonical inclusion of the field into its completion.
file: ArakelovGeometry/ExternalResults/AbsoluteValueTensor.lean
generated: lean
lean_status: lean_ok
title: AbsoluteValue.completionTensorMapOfEq_one_tmul
type: lean
updated: '2026-10-02T11:55:12'
---
theorem completionTensorMapOfEq_one_tmul (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue L ℝ) (h : w.restriction K = v) (a : L) :
    completionTensorMapOfEq v w h (1 ⊗ₜ[K] a) = algebraMap L w.Completion a := by
  subst v
  change completionTensorMap (K := K) w (1 ⊗ₜ[K] a) = _
  simp only [completionTensorMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl
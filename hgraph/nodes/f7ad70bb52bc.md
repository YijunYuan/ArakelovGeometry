---
author: sync
content_type: theorem
created: '2026-10-02T14:15:48'
decl: ArakelovGeometry.AdelicCurve.RationalFunction.finite_support_log_horizontalAbv
docstring: For each nonzero rational function, only finitely many horizontal logarithms
  are nonzero.
file: ArakelovGeometry/AdelicCurve/Examples/RationalFunction/FinitePlaces.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.RationalFunction.finite_support_log_horizontalAbv
type: lean
updated: '2026-10-02T14:15:48'
---
theorem finite_support_log_horizontalAbv {f : RatFunc ℚ} (hf : f ≠ 0) :
    (Function.support fun v : HorizontalPlace ↦ Real.log (horizontalAbv v f)).Finite := by
  have h := (finite_support_log hf).preimage ((Option.some_injective _).injOn)
  apply h.subset
  intro v hv
  change Real.log (pointAbv ℚ (some v) f) ≠ 0
  rw [pointAbv_some, real_log_adicAbv v hf]
  intro hz
  have hz' : WithZero.log (v.valuation (RatFunc ℚ) f) = 0 := by exact_mod_cast hz
  exact hv (by simp [horizontalAbv_apply v hf, hz'])
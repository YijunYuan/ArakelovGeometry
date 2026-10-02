---
author: sync
content_type: theorem
created: '2026-10-02T12:11:38'
decl: ArakelovGeometry.AdelicStructure.logHeight_smul
docstring: Scaling a nonzero tuple adds the integral of the logarithm of the scalar.
file: ArakelovGeometry/AdelicCurve/Height/Basic.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.logHeight_smul
type: lean
updated: '2026-10-02T12:11:38'
---
theorem logHeight_smul {a : ι → K} (ha : a ≠ 0) {t : K} (ht : t ≠ 0) :
    AS.logHeight (t • a) = (∫ ω, Real.log (AS.ϕ ω t) ∂AS.v) + AS.logHeight a := by
  simp only [logHeight, AS.log_localHeight_smul ha ht]
  exact integral_add (AS.integrable_log t ht) (AS.integrable_log_localHeight a)

variable [AS.toAdelicCurve.IsProper]
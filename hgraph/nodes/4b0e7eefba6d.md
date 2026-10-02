---
author: sync
content_type: theorem
created: '2026-10-02T12:11:38'
decl: ArakelovGeometry.AdelicStructure.affineHeight_eq_integral
file: ArakelovGeometry/AdelicCurve/Height/Affine.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.affineHeight_eq_integral
type: lean
updated: '2026-10-02T12:11:38'
---
theorem affineHeight_eq_integral (a : K) :
    AS.affineHeight a = ∫ ω, Real.log (max 1 (AS.ϕ ω a)) ∂AS.v := by
  simp [affineHeight, logHeight, localHeight_pair]
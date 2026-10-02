---
author: sync
content_type: theorem
created: '2026-10-02T12:19:19'
decl: ArakelovGeometry.AdelicStructure.logHeight_algebraicExtension
docstring: Algebraic extension preserves the height of every tuple over the base field.
file: ArakelovGeometry/AdelicCurve/Height/Extension.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.logHeight_algebraicExtension
type: lean
updated: '2026-10-02T12:19:19'
---
theorem logHeight_algebraicExtension (a : ι → K) :
    (AS.algebraicExtension L).logHeight (fun i ↦ algebraMap K L (a i)) =
      AS.logHeight a := by
  change (∫ x, Real.log ((AS.algebraicExtension L).localHeight _ x)
    ∂Algebraic.measure AS L) = AS.logHeight a
  simp_rw [AS.localHeight_algebraicExtension L a]
  exact Algebraic.integral_comp_proj_measure AS L (AS.integrable_log_localHeight a)
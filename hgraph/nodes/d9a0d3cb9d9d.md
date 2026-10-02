---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.projFiniteFiberOfLE_projFiniteFiber
docstring: Fibre projections commute with restriction to a smaller finite stage.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Basic.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.projFiniteFiberOfLE_projFiniteFiber
type: lean
updated: '2026-10-02T11:55:12'
---
theorem projFiniteFiberOfLE_projFiniteFiber {F G : FiniteIntermediateField K L}
    (hFG : F.1 ≤ G.1) (ω : AS.Ω) (x : BaseFiber L ω) :
    projFiniteFiberOfLE hFG ω (projFiniteFiber G ω x) = projFiniteFiber F ω x := by
  apply Subtype.ext
  exact projFiniteOfLE_projFinite AS hFG x.1

omit [Algebra.IsAlgebraic K L] in
---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.projFiniteFiberOfLE
docstring: The finite-stage transition on a fibre preserves its base point.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Basic.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.projFiniteFiberOfLE
type: lean
updated: '2026-10-02T11:55:12'
---
def projFiniteFiberOfLE {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1) (ω : AS.Ω)
    (x : FiniteBaseFiber L G ω) : FiniteBaseFiber L F ω :=
  ⟨projFiniteOfLE AS hFG x.1, x.2⟩

variable {AS L} in
omit [Algebra.IsAlgebraic K L] in
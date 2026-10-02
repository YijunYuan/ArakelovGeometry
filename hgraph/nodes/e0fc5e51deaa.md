---
author: sync
content_type: theorem
created: '2026-10-02T14:16:57'
decl: ArakelovGeometry.AdelicCurve.RationalFunction.adelicStructure_horizontal
file: ArakelovGeometry/AdelicCurve/Examples/RationalFunction/Construction.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.RationalFunction.adelicStructure_horizontal
type: lean
updated: '2026-10-02T14:16:57'
---
theorem adelicStructure_horizontal (v : HorizontalPlace) (f : RatFunc ℚ) :
    adelicStructure.ϕ (Sum.inl (Sum.inl v)) f = horizontalAbv v f := rfl

@[simp]
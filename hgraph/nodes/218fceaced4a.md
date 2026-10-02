---
author: sync
content_type: theorem
created: '2026-10-02T14:16:57'
decl: ArakelovGeometry.AdelicCurve.RationalFunction.augmentedRationalAdelicStructure_horizontal
file: ArakelovGeometry/AdelicCurve/Examples/RationalFunction/Construction.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.RationalFunction.augmentedRationalAdelicStructure_horizontal
type: lean
updated: '2026-10-02T14:16:57'
---
theorem augmentedRationalAdelicStructure_horizontal (v : HorizontalPlace) (a : ℚ) :
    augmentedRationalAdelicStructure.ϕ (Sum.inl (Sum.inl v)) a =
      (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ) a :=
  horizontalAbv_rat v a

@[simp]
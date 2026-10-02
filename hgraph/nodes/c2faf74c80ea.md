---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.not_isNonarchimedeanPlace_mk_infinitePlace
docstring: The class of an infinite place is archimedean.
file: ArakelovGeometry/AdelicCurve/Examples/NumberFields.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.not_isNonarchimedeanPlace_mk_infinitePlace
type: lean
updated: '2026-10-02T11:55:12'
---
theorem not_isNonarchimedeanPlace_mk_infinitePlace (w : InfinitePlace K) :
    ¬IsNonarchimedeanPlace (Quotient.mk' w.val : AbsoluteValue.Place K) := by
  intro hna
  have hout : (Quotient.mk' w.val : AbsoluteValue.Place K).out ≈ w.val :=
    Quotient.mk_out (s := AbsoluteValue.instSetoid) w.val
  exact infinitePlace_not_isNonarchimedean w
    ((isNonarchimedean_congr (hout : _root_.AbsoluteValue.IsEquiv _ _)).mp hna)

open Classical in
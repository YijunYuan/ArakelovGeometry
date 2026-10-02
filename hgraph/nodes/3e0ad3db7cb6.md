---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.isNonarchimedeanPlace_mk_finitePlace
docstring: The class of a finite place is nonarchimedean.
file: ArakelovGeometry/AdelicCurve/Examples/NumberFields.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.isNonarchimedeanPlace_mk_finitePlace
type: lean
updated: '2026-10-02T11:55:12'
---
theorem isNonarchimedeanPlace_mk_finitePlace (v : FinitePlace K) :
    IsNonarchimedeanPlace (Quotient.mk' v.val : AbsoluteValue.Place K) := by
  have hout : (Quotient.mk' v.val : AbsoluteValue.Place K).out ≈ v.val :=
    Quotient.mk_out (s := AbsoluteValue.instSetoid) v.val
  exact (isNonarchimedean_congr (hout : _root_.AbsoluteValue.IsEquiv _ _)).mpr
    (finitePlace_isNonarchimedean v)

omit [NumberField K] in
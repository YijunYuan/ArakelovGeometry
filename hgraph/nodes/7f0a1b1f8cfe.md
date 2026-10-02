---
author: sync
content_type: theorem
created: '2026-10-02T14:15:48'
decl: ArakelovGeometry.AdelicCurve.RationalFunction.not_isNonarchimedean_archimedeanAbv
file: ArakelovGeometry/AdelicCurve/Examples/RationalFunction/Archimedean.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.RationalFunction.not_isNonarchimedean_archimedeanAbv
type: lean
updated: '2026-10-02T14:15:48'
---
theorem not_isNonarchimedean_archimedeanAbv (t : ArchimedeanPlace) :
    ¬IsNonarchimedean (archimedeanAbv t) := by
  intro h
  have htwo := archimedeanAbv_rat t 2
  norm_num [Rat.AbsoluteValue.real_eq_abs] at htwo
  have hone := h 1 1
  norm_num [show (1 : RatFunc ℚ) + 1 = 2 by norm_num, htwo] at hone
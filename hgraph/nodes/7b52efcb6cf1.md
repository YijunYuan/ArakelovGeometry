---
author: sync
content_type: definition
created: '2026-10-02T12:19:19'
decl: ArakelovGeometry.AdelicStructure.polynomialLocalHeight
docstring: The maximum of the absolute values of all coefficients of a polynomial.
file: ArakelovGeometry/AdelicCurve/Height/Polynomial.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.polynomialLocalHeight
type: lean
updated: '2026-10-02T12:19:19'
---
noncomputable def polynomialLocalHeight (p : K[X]) (ω : AS.Ω) : ℝ :=
  AS.localHeight (fun i : Fin (p.natDegree + 1) ↦ p.coeff i) ω
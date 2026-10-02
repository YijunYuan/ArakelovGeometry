---
author: sync
content_type: class
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicCurve.IsProper
docstring: 'An adelic curve is *proper* if the product formula holds for all nonzero
  elements

  of `K` (Chen–Moriwaki, §3.1).'
file: ArakelovGeometry/AdelicCurve/Defs.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.IsProper
type: lean
updated: '2026-10-02T11:55:12'
---
class IsProper (C : AdelicCurve) where
  /-- The product formula. -/
  product_formula : ∀ x : C.K, x ≠ 0 → ∫ ω, Real.log ((C.AS.ϕ ω) x) ∂C.AS.v = 0
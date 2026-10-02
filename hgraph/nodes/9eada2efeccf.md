---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicCurve.isProper_fRestriction
docstring: 'Properness is inherited by the restriction to a subfield: the product
  formula for

  `F ⊆ K` is a special case of the one for `K`.'
file: ArakelovGeometry/AdelicCurve/Restriction.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.isProper_fRestriction
type: lean
updated: '2026-10-02T11:55:12'
---
theorem isProper_fRestriction {AC : AdelicCurve} [IsProper AC] (F : Subfield AC.K) :
    IsProper (AC.fRestriction F) := by
  constructor
  intro x hx
  have hx' : F.subtype x ≠ 0 := fun h ↦
    hx (F.subtype.injective (h.trans (map_zero F.subtype).symm))
  exact IsProper.product_formula (C := AC) (F.subtype x) hx'
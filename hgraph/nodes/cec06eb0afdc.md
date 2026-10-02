---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.placeRep
docstring: 'The canonical (normalized) representative of a place: the trivial absolute
  value for the

  trivial place, the mathlib `FinitePlace` value for nonarchimedean places, the mathlib

  `InfinitePlace` value for archimedean ones.'
file: ArakelovGeometry/AdelicCurve/Examples/NumberFields.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.placeRep
type: lean
updated: '2026-10-02T11:55:12'
---
noncomputable def placeRep (ω : AbsoluteValue.Place K) : AbsoluteValue K ℝ :=
  if hp : ω = trivialPlace K then .trivial
  else if hna : IsNonarchimedeanPlace ω then ((isNonarchimedeanPlace_iff ω hp).mp hna).choose.val
  else ((isArchimedeanPlace_iff ω).mp hna).choose.val

open Classical in
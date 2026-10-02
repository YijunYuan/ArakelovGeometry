---
author: sync
content_type: structure
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.FiniteIntermediateField
docstring: 'The filtered indexing type `E_{L/K}` of finite subextensions of an algebraic
  extension

  `L/K`.'
file: ArakelovGeometry/AdelicCurve/Extension/FiniteIntermediateField.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.FiniteIntermediateField
type: lean
updated: '2026-10-02T11:55:12'
---
structure FiniteIntermediateField (K : Type u) [Field K] (L : Type w) [Field L]
    [Algebra K L] extends IntermediateField K L where
  finite_dimensional : FiniteDimensional K toIntermediateField

attribute [instance] FiniteIntermediateField.finite_dimensional
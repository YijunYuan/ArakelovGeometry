---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension.measure
docstring: 'The measure on the finite extension `S ⊗_K L`: it is the measure already
  constructed on the

  finite separable extension `K''/K`.'
file: ArakelovGeometry/AdelicCurve/Extension/Finite/Construction.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension.measure
type: lean
updated: '2026-10-02T11:55:12'
---
noncomputable def measure : Measure (ParameterSpaceFinExtension AS L) :=
  ParameterSpaceExtension.inducedMeasure AS (separableClosure K L)
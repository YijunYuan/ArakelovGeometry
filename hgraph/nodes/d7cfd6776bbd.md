---
author: sync
content_type: definition
created: '2026-10-02T14:15:48'
decl: ArakelovGeometry.AdelicCurve.RationalFunction.archimedeanMeasure
docstring: Lebesgue measure on the transcendental unit-circle parameters.
file: ArakelovGeometry/AdelicCurve/Examples/RationalFunction/Archimedean.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.RationalFunction.archimedeanMeasure
type: lean
updated: '2026-10-02T14:15:48'
---
noncomputable def archimedeanMeasure : Measure ArchimedeanPlace := volume.comap Subtype.val

instance : IsProbabilityMeasure archimedeanMeasure where
  measure_univ := by
    rw [archimedeanMeasure,
      (MeasurableEmbedding.subtype_coe measurableSet_archimedeanDomain).comap_apply]
    simpa using volume_archimedeanDomain
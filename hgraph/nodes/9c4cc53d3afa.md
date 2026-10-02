---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicCurve.trivialAdelicStructure
docstring: 'The trivial adelic structure on `K` over a measure space `(Ω, A, v)`:
  every point

  carries the trivial absolute value.'
file: ArakelovGeometry/AdelicCurve/Examples/Trivial.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.trivialAdelicStructure
type: lean
updated: '2026-10-02T11:55:12'
---
noncomputable def trivialAdelicStructure (K : Type*) [Field K]
    (Ω : Type*) [A : MeasurableSpace Ω] (v : Measure Ω) : AdelicStructure K where
  Ω := Ω
  A := A
  v := v
  ϕ := fun _ ↦ AbsoluteValue.trivial
  measurable_log := fun _ _ ↦ measurable_const
  integrable_log := fun a ha ↦ by
    simp only [AbsoluteValue.trivial_apply ha, Real.log_one]
    exact integrable_zero _ _ _
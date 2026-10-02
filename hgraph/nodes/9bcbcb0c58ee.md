---
author: sync
content_type: instance
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.extensionFiber_separatesPoints
docstring: Evaluation maps distinguish two different absolute values in the same fibre.
file: ArakelovGeometry/AdelicCurve/Extension/ParameterSpace.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.extensionFiber_separatesPoints
type: lean
updated: '2026-10-02T11:55:12'
---
instance extensionFiber_separatesPoints (ω : AS.Ω) :
    MeasurableSpace.SeparatesPoints (ExtensionFiber AS L ω) := by
  rw [MeasurableSpace.separatesPoints_iff]
  intro x y h
  apply Subtype.ext
  apply ext AS L (x.property.trans y.property.symm)
  ext a
  have hmeas : Measurable fun z : ExtensionFiber AS L ω ↦ z.val.ϕ a :=
    (measurable_eval AS L a).comp measurable_subtype_coe
  exact ((h {z | z.val.ϕ a = x.val.ϕ a}
    (hmeas (measurableSet_singleton _))).mp rfl).symm
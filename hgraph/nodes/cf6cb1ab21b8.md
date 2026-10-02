---
author: sync
content_type: definition
created: '2026-10-02T14:02:34'
decl: ArakelovGeometry.AdelicCurve.Hom.algebraicExtension
docstring: 'Chen–Moriwaki, Example 3.7.2 (1): an algebraic extension gives a morphism

  back to the original adelic curve, with its prescribed fibre-integration operator.'
file: ArakelovGeometry/AdelicCurve/Morphism/Algebraic.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.Hom.algebraicExtension
type: lean
updated: '2026-10-02T14:02:34'
---
noncomputable def algebraicExtension :
    Hom (AS.algebraicExtension L).toAdelicCurve AS.toAdelicCurve where
  fieldMap := algebraMap K L
  baseMap := ParameterSpaceExtension.proj
  measurePreserving := Algebraic.measurePreserving_proj AS L
  absoluteValue_comp x a :=
    congrArg (fun v : AbsoluteValue K ℝ ↦ v a) x.restrict_eq
  fibreIntegral := (Algebraic.fibreIntegralL1ContinuousLinearMap AS L).toLinearMap
  integral_fibreIntegral := Algebraic.integral_fibreIntegralL1 AS L
  fibreIntegral_pullback := Algebraic.fibreIntegralL1_compMeasurePreserving AS L

/-- The field map of the algebraic-extension morphism is the field inclusion. -/
@[simp]
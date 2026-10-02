---
author: sync
content_type: theorem
created: '2026-10-02T13:11:44'
decl: Projectivization.fieldOfDefinition_eq_adjoin
docstring: Formula for the field of definition in any nonzero affine chart.
file: ArakelovGeometry/AdelicCurve/Height/Projective.lean
generated: lean
lean_status: lean_ok
title: Projectivization.fieldOfDefinition_eq_adjoin
type: lean
updated: '2026-10-02T13:11:44'
---
theorem fieldOfDefinition_eq_adjoin (x : Projectivization L (ι → L))
    {j : ι} (hj : x.rep j ≠ 0) :
    fieldOfDefinition K x =
      IntermediateField.adjoin K (Set.range fun i ↦ x.rep i / x.rep j) := by
  rw [fieldOfDefinition_eq, coordinateField_eq_adjoin K _ hj]
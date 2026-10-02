---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AbsoluteValue.coe_smul_completion
docstring: 'The coercion `WithAbs v → v.Completion` is semilinear over the scalar
  action of

  `(v.restriction L).Completion`.'
file: ArakelovGeometry/ExternalResults/AbsoluteValue.lean
generated: lean
lean_status: lean_ok
title: AbsoluteValue.coe_smul_completion
type: lean
updated: '2026-10-02T11:55:12'
---
theorem coe_smul_completion (c : WithAbs (v.restriction L)) (y : WithAbs v) :
    ((c • y : WithAbs v) : v.Completion)
      = (c : (v.restriction L).Completion) • (y : v.Completion) := by
  rw [Algebra.smul_def, Algebra.smul_def, UniformSpace.Completion.coe_mul,
    algebraMap_completion_def, UniformSpace.Completion.mapRingHom_coe]
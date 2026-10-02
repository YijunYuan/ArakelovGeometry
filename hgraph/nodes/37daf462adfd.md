---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AbsoluteValue.norm_algebraMap_completion
docstring: The algebra map between the completions preserves the norm.
file: ArakelovGeometry/ExternalResults/AbsoluteValue.lean
generated: lean
lean_status: lean_ok
title: AbsoluteValue.norm_algebraMap_completion
type: lean
updated: '2026-10-02T11:55:12'
---
theorem norm_algebraMap_completion (a : (v.restriction L).Completion) :
    ‖algebraMap (v.restriction L).Completion v.Completion a‖ = ‖a‖ := by
  simpa using (isometry_algebraMap_completion v L).norm_map_of_map_zero (map_zero _) a

/-- `v.Completion` is a normed space over `(v.restriction L).Completion`. -/
noncomputable instance : NormedSpace (v.restriction L).Completion v.Completion where
  norm_smul_le a b := by
    rw [Algebra.smul_def, norm_mul, norm_algebraMap_completion]
---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.DescendsToFinite.nonempty_smul
docstring: 'Remark 3.4.7: the cylinder functions `V_L` are closed under scalar multiplication.'
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/CylinderContent.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.DescendsToFinite.nonempty_smul
type: lean
updated: '2026-10-02T11:55:12'
---
theorem DescendsToFinite.nonempty_smul (c : ℝ) {f : ParameterSpaceExtension AS L → ℝ}
    (hf : DescendsToFinite AS L f) : Nonempty (DescendsToFinite AS L (c • f)) := by
  refine ⟨⟨hf.F, fun x ↦ c * hf.g x, ?_⟩⟩
  ext x
  simp only [hf.eq_comp, Pi.smul_apply, Function.comp_apply, smul_eq_mul]

variable {AS L} in
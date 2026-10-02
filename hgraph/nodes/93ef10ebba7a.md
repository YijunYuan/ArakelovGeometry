---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreIntegral_eq_sum
docstring: Real fibre integration is the finite sum with its local-degree weights.
file: ArakelovGeometry/AdelicCurve/Extension/Separable/FibreIntegral.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.fibreIntegral_eq_sum
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreIntegral_eq_sum (f : ParameterSpaceExtension AS L → ℝ) (ω : AS.Ω)
    [Fintype (ExtensionFiber AS L ω)] :
    fibreIntegral AS L f ω =
      ∑ x : ExtensionFiber AS L ω, (fibreWeight AS L ω x).toReal * f x.val := by
  unfold fibreIntegral fibreProbabilityMeasure
  rw [integral_sum_measure (integrable_fibre AS L ω _), tsum_fintype]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]

omit [Algebra.IsSeparable K L] in
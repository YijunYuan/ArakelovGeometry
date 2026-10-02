---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.fibreIntegral_comp_proj
docstring: 'Remark 3.4.7: fibre integration retracts the pullback along the base projection:

  `I_{L/K}(g ∘ π_{L/K}) = g`.'
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/Measure.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.fibreIntegral_comp_proj
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreIntegral_comp_proj (g : AS.Ω → ℝ) :
    fibreIntegral AS L (fun x ↦ g (ParameterSpaceExtension.proj x)) = g := by
  funext ω
  calc
    _ = ∫ _ : BaseFiber L ω, g ω ∂fibreProbabilityMeasure AS L ω :=
      integral_congr_ae (Filter.Eventually.of_forall fun x ↦ congrArg g x.property)
    _ = g ω := by simp
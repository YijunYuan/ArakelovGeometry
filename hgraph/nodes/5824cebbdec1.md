---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.map_inducedMeasure_proj
docstring: The projection sends the induced measure to the base measure.
file: ArakelovGeometry/AdelicCurve/Extension/Separable/Measure.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.map_inducedMeasure_proj
type: lean
updated: '2026-10-02T11:55:12'
---
theorem map_inducedMeasure_proj :
    Measure.map (ParameterSpaceExtension.proj (AS := AS) (L := L)) (inducedMeasure AS L) =
      AS.v := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_proj AS L) hs, inducedMeasure_apply AS L
    (hs.preimage (measurable_proj AS L))]
  have hconst (ω : AS.Ω) :
      fibreLIntegral AS L ((proj ⁻¹' s).indicator fun _ ↦ 1) ω =
        s.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
    change (∫⁻ x : ExtensionFiber AS L ω,
      (proj ⁻¹' s).indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val
        ∂fibreProbabilityMeasure AS L ω) = _
    classical
    simp only [Set.indicator, Set.mem_preimage]
    simp_rw [show ∀ x : ExtensionFiber AS L ω, x.val.proj = ω from fun x ↦ x.property]
    simp
  simp_rw [hconst]
  rw [lintegral_indicator_const hs, one_mul]
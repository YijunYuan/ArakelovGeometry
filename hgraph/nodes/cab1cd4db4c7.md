---
author: sync
content_type: theorem
created: '2026-10-02T13:32:55'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.measurable_fibreMaximum
docstring: 'Chen--Moriwaki, Proposition 3.6.2: maxima over finite extension fibres
  are

  measurable for every measurable real function, without normality or separability.'
file: ArakelovGeometry/AdelicCurve/Extension/FibreMaximum.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceExtension.measurable_fibreMaximum
type: lean
updated: '2026-10-02T13:32:55'
---
theorem measurable_fibreMaximum {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable f) : Measurable (fibreMaximum AS L f) := by
  apply measurable_of_Ioi
  intro c
  have heq : fibreMaximum AS L f ⁻¹' Set.Ioi c = proj '' (f ⁻¹' Set.Ioi c) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ioi, lt_fibreMaximum_iff, Set.mem_image]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.val, hx, x.property⟩,
      fun ⟨x, hx, hω⟩ ↦ ⟨⟨x, hω⟩, hx⟩⟩
  rw [heq]
  exact measurableSet_image_proj AS L (hf measurableSet_Ioi)
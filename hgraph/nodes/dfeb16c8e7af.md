---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.Algebraic.fibreCylinderContent_preimage
docstring: The cylinder content agrees with each prescribed finite-stage probability.
file: ArakelovGeometry/AdelicCurve/Extension/Algebraic/CylinderContent.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.Algebraic.fibreCylinderContent_preimage
type: lean
updated: '2026-10-02T11:55:12'
---
theorem fibreCylinderContent_preimage (ω : AS.Ω) (F : FiniteIntermediateField K L)
    (B : Set (FiniteBaseFiber L F ω)) :
    fibreCylinderContent AS L ω (projFiniteFiber F ω ⁻¹' B) =
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω B := by
  apply le_antisymm
  · exact iInf_le_of_le F (iInf_le_of_le B (iInf_le_of_le (Set.Subset.refl _) le_rfl))
  · exact le_iInf fun G ↦ le_iInf fun C ↦ le_iInf fun hBC ↦
      finiteFibreProbabilityMeasure_le_of_preimage_subset AS L ω F G B C hBC
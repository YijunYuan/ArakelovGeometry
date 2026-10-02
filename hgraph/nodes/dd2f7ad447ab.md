---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension.lintegral_measure
docstring: Nonnegative disintegration for a finite, possibly inseparable extension.
file: ArakelovGeometry/AdelicCurve/Extension/Finite/Tower.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension.lintegral_measure
type: lean
updated: '2026-10-02T11:55:12'
---
theorem lintegral_measure {f : ParameterSpaceFinExtension AS L → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂(AS.finiteExtension L).v = ∫⁻ ω, fibreLIntegral AS L f ω ∂AS.v :=
  ParameterSpaceExtension.lintegral_inducedMeasure AS (separableClosure K L) hf

end ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension


namespace ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension
variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
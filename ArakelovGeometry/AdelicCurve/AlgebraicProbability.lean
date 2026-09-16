/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension

/-!
# Uniqueness of algebraic fibre measures

Finite-stage marginals determine a finite measure on the cylinder sigma algebra.
In particular they characterize the fibre probability of Chen–Moriwaki,
Proposition 3.4.6.
-/

open MeasureTheory

namespace ArakelovGeometry.AdelicStructure.Algebraic

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

omit [Algebra.IsAlgebraic K L] in
/-- Two measures on an algebraic fibre agree when one is finite and all their finite-stage
pushforwards agree. -/
theorem fibreMeasure_ext (ω : AS.Ω)
    {μ ν : @Measure (BaseFiber L ω) (fibreMeasurableSpace L ω)}
    [@IsFiniteMeasure (BaseFiber L ω) (fibreMeasurableSpace L ω) μ]
    (h : ∀ F : FiniteIntermediateField K L,
      @Measure.map (BaseFiber L ω) (FiniteBaseFiber L F ω)
        (fibreMeasurableSpace L ω) inferInstance (projFiniteFiber F ω) μ =
      @Measure.map (BaseFiber L ω) (FiniteBaseFiber L F ω)
        (fibreMeasurableSpace L ω) inferInstance (projFiniteFiber F ω) ν) :
    μ = ν := by
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  have hcyl : ∀ A ∈ fibreCylinders AS L ω, μ A = ν A := by
    rintro A ⟨F, B, rfl⟩
    have hB := measurableSet_finiteBaseFiber AS L F ω B
    rw [← Measure.map_apply (measurable_projFiniteFiber AS L ω F) hB,
      ← Measure.map_apply (measurable_projFiniteFiber AS L ω F) hB, h F]
  exact ext_of_generate_finite (fibreCylinders AS L ω)
    (fibreMeasurableSpace_eq_generateFrom AS L ω)
    (fun A hA B hB _ ↦ (isSetAlgebra_fibreCylinders AS L ω).inter_mem hA hB)
    hcyl (hcyl _ (isSetAlgebra_fibreCylinders AS L ω).univ_mem)

/-- The prescribed finite-stage marginals characterize the algebraic fibre probability.
No normalization assumption is necessary: the marginals determine the total mass. -/
theorem eq_fibreProbabilityMeasure_of_map_projFiniteFiber (ω : AS.Ω)
    {μ : @Measure (BaseFiber L ω) (fibreMeasurableSpace L ω)}
    (h : ∀ F : FiniteIntermediateField K L,
      @Measure.map (BaseFiber L ω) (FiniteBaseFiber L F ω)
        (fibreMeasurableSpace L ω) inferInstance (projFiniteFiber F ω) μ =
      ParameterSpaceFinExtension.fibreProbabilityMeasure AS F ω) :
    μ = fibreProbabilityMeasure AS L ω := by
  symm
  apply fibreMeasure_ext AS L ω
  intro F
  rw [map_fibreProbabilityMeasure_projFiniteFiber, h F]

end ArakelovGeometry.AdelicStructure.Algebraic

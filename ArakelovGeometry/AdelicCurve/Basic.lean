import ArakelovGeometry.AdelicCurve.Defs

namespace ArakelovGeometry
namespace AdelicStructure
open MeasureTheory

-- Proposition 3.1.1
theorem Ωinf_measurable {K : Type u_1} [Field K] (AS : AdelicStructure K) :
  AS.A.MeasurableSet' AS.Ωinf := by
  sorry

-- Proposition 3.1.2 (1)
theorem κ_measurable {K : Type u_1} [Field K] (AS : AdelicStructure K) : Measurable AS.κ := by
  sorry

-- Proposition 3.1.2 (2)
theorem κ_integrable {K : Type u_1} [Field K] (AS : AdelicStructure K) : Integrable AS.κ AS.v := by
  sorry

-- Proposition 3.1.2 (3)
theorem v_Ωinf_finite_of_κ_bddBelow {K : Type u_1} [Field K] (AS : AdelicStructure K) (hκ : ∃ (ε : ℝ), ε > 0 ∧ ε ∈ lowerBounds (AS.κ '' AS.Ωinf)) : AS.v AS.Ωinf < ⊤ := by
  sorry

open Classical in
-- Proposition 3.1.3
theorem measurable_of_trivial_abs {K : Type u_1} [Field K] [Countable K] (AS : AdelicStructure K) :
  AS.A.MeasurableSet' {ω : AS.Ω | AS.ϕ ω = AbsoluteValue.trivial} := by
  sorry


end AdelicStructure
end ArakelovGeometry

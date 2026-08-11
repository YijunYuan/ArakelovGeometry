import ArakelovGeometry.AdelicCurve.Basic

namespace ArakelovGeometry.AdelicCurve
open MeasureTheory AbsoluteValue

open Classical in
noncomputable def TrivialAdelicStructure (K : Type u_1) [Field K]
  (Ω : Type u_2) [A : MeasurableSpace Ω] (v : Measure Ω) : AdelicStructure K where
  Ω := Ω
  A := A
  v := v
  ϕ := fun _ => AbsoluteValue.trivial
  hφ1 := fun _ _ => measurable_const
  hφ2 := fun a ha => by
    simp only [AbsoluteValue.trivial_apply ha, Real.log_one]
    exact integrable_zero _ _ _

noncomputable abbrev TrivialAdelicCurve (K : Type u_1) [Field K]
  (Ω : Type u_2) [A : MeasurableSpace Ω] (v : Measure Ω) : AdelicCurve :=
  (TrivialAdelicStructure K Ω v).toAdelicCurve

open Classical in
noncomputable instance (K : Type u_1) [Field K] (Ω : Type u_2) [A : MeasurableSpace Ω]
  (v : Measure Ω) : IsProper (TrivialAdelicCurve K Ω v) := by
  constructor
  intro x hx
  -- the integrand is identically `log 1 = 0`
  have key : ∀ y : K, y ≠ 0 →
      ∫ _ω : Ω, Real.log ((AbsoluteValue.trivial : AbsoluteValue K ℝ) y) ∂v = 0 := by
    intro y hy
    rw [AbsoluteValue.trivial_apply hy, Real.log_one, integral_zero]
  exact key x hx

end ArakelovGeometry.AdelicCurve

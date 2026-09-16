/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Basic

/-!
# The trivial adelic structure

Any measure space `(Ω, A, v)` yields an adelic structure on any field `K` by assigning the
trivial absolute value to every point.  The resulting adelic curve is proper: the integrand
of the product formula vanishes identically.
-/

namespace ArakelovGeometry.AdelicCurve

open MeasureTheory AbsoluteValue

open Classical in
/-- The trivial adelic structure on `K` over a measure space `(Ω, A, v)`: every point
carries the trivial absolute value. -/
noncomputable def trivialAdelicStructure (K : Type*) [Field K]
    (Ω : Type*) [A : MeasurableSpace Ω] (v : Measure Ω) : AdelicStructure K where
  Ω := Ω
  A := A
  v := v
  ϕ := fun _ ↦ AbsoluteValue.trivial
  measurable_log := fun _ _ ↦ measurable_const
  integrable_log := fun a ha ↦ by
    simp only [AbsoluteValue.trivial_apply ha, Real.log_one]
    exact integrable_zero _ _ _

/-- The trivial adelic curve on `K` over a measure space `(Ω, A, v)`. -/
noncomputable abbrev trivialAdelicCurve (K : Type*) [Field K]
    (Ω : Type*) [A : MeasurableSpace Ω] (v : Measure Ω) : AdelicCurve :=
  (trivialAdelicStructure K Ω v).toAdelicCurve

open Classical in
/-- The trivial adelic curve is proper: the integrand of the product formula vanishes
identically. -/
noncomputable instance instIsProperTrivialAdelicCurve
    (K : Type*) [Field K] (Ω : Type*) [A : MeasurableSpace Ω]
    (v : Measure Ω) : IsProper (trivialAdelicCurve K Ω v) := by
  constructor
  intro x hx
  -- the integrand is identically `log 1 = 0`
  have key : ∀ y : K, y ≠ 0 →
      ∫ _ω : Ω, Real.log ((AbsoluteValue.trivial : AbsoluteValue K ℝ) y) ∂v = 0 := by
    intro y hy
    rw [AbsoluteValue.trivial_apply hy, Real.log_one, integral_zero]
  exact key x hx

end ArakelovGeometry.AdelicCurve

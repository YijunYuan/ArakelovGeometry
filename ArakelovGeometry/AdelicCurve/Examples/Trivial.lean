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


    sorry

noncomputable abbrev TrivialAdelicCurve (K : Type u_1) [Field K]
  (Ω : Type u_2) [A : MeasurableSpace Ω] (v : Measure Ω) : AdelicCurve :=
  (TrivialAdelicStructure K Ω v).toAdelicCurve

noncomputable instance (K : Type u_1) [Field K] (Ω : Type u_2) [A : MeasurableSpace Ω]
  (v : Measure Ω) : IsProper (TrivialAdelicCurve K Ω v) := by
  sorry

end ArakelovGeometry.AdelicCurve

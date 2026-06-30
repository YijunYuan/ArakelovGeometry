import ArakelovGeometry.AdelicCurve.Basic
import Mathlib.MeasureTheory.Measure.Restrict

namespace ArakelovGeometry

namespace AdelicStructure

-- Sec 3.2.8 `Restriction of adelic structure to a subfield`
def fRestriction {K : Type u_1} [Field K] (AS : AdelicStructure K) (F : Subfield K) :
  AdelicStructure F where
  Ω := AS.Ω
  A := AS.A
  v := AS.v
  ϕ ω := sorry -- restriction of AS.ϕ ω to F
  hφ1 := sorry
  hφ2 := sorry

-- Sec 3.2.9 `Restriction of adelic structure to a measurable subset`
def sRestriction {K : Type u_1} [Field K] (AS : AdelicStructure K)
  (Ω₀ : Set AS.Ω) (hΩ₀ : MeasurableSet Ω₀) :
  AdelicStructure K where
  Ω := Ω₀
  A := sorry
  v := sorry
  ϕ ω := AS.ϕ ω
  hφ1 := sorry
  hφ2 := sorry

end AdelicStructure

namespace AdelicCurve

abbrev fRestriction (AC : AdelicCurve) (F : Subfield AC.K) : AdelicCurve :=
  (AC.AS.fRestriction F).toAdelicCurve

theorem isProper_of_fRestriction {AC : AdelicCurve} [IsProper AC] (F : Subfield AC.K) :
  IsProper (AC.fRestriction F) := by
  sorry

abbrev sRestriction (AC : AdelicCurve) (Ω₀ : Set AC.AS.Ω) (hΩ₀ : MeasurableSet Ω₀) :
  AdelicCurve :=
  (AC.AS.sRestriction Ω₀ hΩ₀).toAdelicCurve

end AdelicCurve

end ArakelovGeometry

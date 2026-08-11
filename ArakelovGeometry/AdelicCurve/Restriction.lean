import ArakelovGeometry.AdelicCurve.Basic
import Mathlib.MeasureTheory.Measure.Restrict

namespace ArakelovGeometry

open MeasureTheory

namespace AdelicStructure

-- Sec 3.2.8 `Restriction of adelic structure to a subfield`
def fRestriction {K : Type u_1} [Field K] (AS : AdelicStructure K) (F : Subfield K) :
  AdelicStructure F where
  Ω := AS.Ω
  A := AS.A
  v := AS.v
  ϕ ω := (AS.ϕ ω).restriction F -- restriction of AS.ϕ ω to F
  hφ1 x hx := AS.hφ1 (x : K) (by exact_mod_cast hx)
  hφ2 x hx := AS.hφ2 (x : K) (by exact_mod_cast hx)

-- Sec 3.2.9 `Restriction of adelic structure to a measurable subset`
noncomputable def sRestriction {K : Type u_1} [Field K] (AS : AdelicStructure K)
  (Ω₀ : Set AS.Ω) (hΩ₀ : MeasurableSet Ω₀) :
  AdelicStructure K where
  Ω := Ω₀
  A := Subtype.instMeasurableSpace
  v := AS.v.comap Subtype.val
  ϕ ω := AS.ϕ ω
  hφ1 x hx := (AS.hφ1 x hx).comp measurable_subtype_coe
  hφ2 x hx := by
    have h : Integrable ((fun ω : AS.Ω => Real.log ((AS.ϕ ω) x)) ∘ (Subtype.val : Ω₀ → AS.Ω))
        (AS.v.comap Subtype.val) := by
      rw [← (MeasurableEmbedding.subtype_coe hΩ₀).integrable_map_iff,
        map_comap_subtype_coe hΩ₀]
      exact (AS.hφ2 x hx).restrict
    exact h

end AdelicStructure

namespace AdelicCurve

abbrev fRestriction (AC : AdelicCurve) (F : Subfield AC.K) : AdelicCurve :=
  (AC.AS.fRestriction F).toAdelicCurve

theorem isProper_of_fRestriction {AC : AdelicCurve} [IsProper AC] (F : Subfield AC.K) :
  IsProper (AC.fRestriction F) := by
  constructor
  intro x hx
  have hx' : F.subtype x ≠ 0 := fun h =>
    hx (F.subtype.injective (h.trans (map_zero F.subtype).symm))
  exact IsProper.product_formula (C := AC) (F.subtype x) hx'

noncomputable abbrev sRestriction (AC : AdelicCurve) (Ω₀ : Set AC.AS.Ω)
  (hΩ₀ : MeasurableSet Ω₀) : AdelicCurve :=
  (AC.AS.sRestriction Ω₀ hΩ₀).toAdelicCurve

end AdelicCurve

end ArakelovGeometry

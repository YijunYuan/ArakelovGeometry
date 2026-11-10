/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Basic
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Restriction of adelic structures

Following Chen–Moriwaki, §3.2.8 and §3.2.9, an adelic structure on `K` restricts to a
subfield `F ⊆ K` (restrict every absolute value) and to a measurable subset `Ω₀` of the
index space (restrict the measure).  Properness is inherited by the restriction to a
subfield.
-/

@[expose] public section

namespace ArakelovGeometry

open MeasureTheory

namespace AdelicStructure

/-- The restriction of an adelic structure on `K` to a subfield `F` (Chen–Moriwaki,
§3.2.8): keep the measure space and restrict every absolute value to `F`. -/
def fRestriction {K : Type*} [Field K] (AS : AdelicStructure K) (F : Subfield K) :
    AdelicStructure F where
  Ω := AS.Ω
  A := AS.A
  v := AS.v
  ϕ ω := (AS.ϕ ω).under F
  measurable_log x hx := AS.measurable_log (x : K) (by exact_mod_cast hx)
  integrable_log x hx := AS.integrable_log (x : K) (by exact_mod_cast hx)

/-- Properness is inherited by the restriction to a subfield: the product formula for
`F ⊆ K` is a special case of the one for `K`. -/
theorem isProper_fRestriction {K : Type*} [Field K] {AS : AdelicStructure K}
    [AS.IsProper] (F : Subfield K) : (AS.fRestriction F).IsProper := by
  constructor
  intro x hx
  have hx' : F.subtype x ≠ 0 := fun h ↦
    hx (F.subtype.injective (h.trans (map_zero F.subtype).symm))
  exact IsProper.product_formula (AS := AS) (F.subtype x) hx'

/-- The restriction of an adelic structure to a measurable subset `Ω₀` of its index space
(Chen–Moriwaki, §3.2.9): keep the absolute values and restrict the measure to `Ω₀`. -/
noncomputable def sRestriction {K : Type*} [Field K] (AS : AdelicStructure K)
    (Ω₀ : Set AS.Ω) (hΩ₀ : MeasurableSet Ω₀) :
    AdelicStructure K where
  Ω := Ω₀
  A := Subtype.instMeasurableSpace
  v := AS.v.comap Subtype.val
  ϕ ω := AS.ϕ ω
  measurable_log x hx := (AS.measurable_log x hx).comp measurable_subtype_coe
  integrable_log x hx := by
    have h : Integrable ((fun ω : AS.Ω ↦ Real.log ((AS.ϕ ω) x)) ∘ (Subtype.val : Ω₀ → AS.Ω))
        (AS.v.comap Subtype.val) := by
      rw [← (MeasurableEmbedding.subtype_coe hΩ₀).integrable_map_iff,
        map_comap_subtype_coe hΩ₀]
      exact (AS.integrable_log x hx).restrict
    exact h

end AdelicStructure

namespace AdelicCurve

/-- The restriction of an adelic curve to a subfield of its base field. -/
abbrev fRestriction (AC : AdelicCurve) (F : Subfield AC.K) : AdelicCurve :=
  (AC.AS.fRestriction F).toAdelicCurve

/-- Properness of a bundled curve is inherited by restriction to a subfield. -/
theorem isProper_fRestriction {AC : AdelicCurve} [IsProper AC] (F : Subfield AC.K) :
    IsProper (AC.fRestriction F) :=
  AdelicStructure.isProper_fRestriction (AS := AC.AS) F

/-- The restriction of an adelic curve to a measurable subset of its index space. -/
noncomputable abbrev sRestriction (AC : AdelicCurve) (Ω₀ : Set AC.AS.Ω)
    (hΩ₀ : MeasurableSet Ω₀) : AdelicCurve :=
  (AC.AS.sRestriction Ω₀ hΩ₀).toAdelicCurve

end AdelicCurve

end ArakelovGeometry

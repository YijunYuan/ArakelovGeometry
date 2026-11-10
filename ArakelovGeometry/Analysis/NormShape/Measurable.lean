/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.NormShape.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Measurable families of convex norm profiles

The source measures profiles in the uniform topology on continuous functions
on `[0,1]`. We use the canonical restriction of a `NormShape` to this compact
interval, so its irrelevant values outside the interval are not measured.
-/

@[expose] public section

namespace ArakelovGeometry.NormShape

/-- A norm profile as a continuous function on the source's compact interval. -/
def continuousMap (ψ : NormShape) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun t ↦ ψ.toFun t, continuousOn_iff_continuous_domRestrict.mp ψ.continuousOn⟩

local instance : MeasurableSpace C(Set.Icc (0 : ℝ) 1, ℝ) := borel _
local instance : BorelSpace C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨rfl⟩

/-- Source measurability for profile families: the Borel structure of uniform convergence. -/
def IsMeasurableFamily {Ω : Type*} [MeasurableSpace Ω] (ψ : Ω → NormShape) : Prop :=
  Measurable (fun ω ↦ (ψ ω).continuousMap)

/-- A measurable varying profile evaluated at a measurable interval-valued point is measurable. -/
theorem IsMeasurableFamily.eval {Ω : Type*} [MeasurableSpace Ω] {ψ : Ω → NormShape}
    (hψ : IsMeasurableFamily ψ) {t : Ω → Set.Icc (0 : ℝ) 1} (ht : Measurable t) :
    Measurable (fun ω ↦ (ψ ω).toFun (t ω)) := by
  have hc : Continuous (fun z : C(Set.Icc (0 : ℝ) 1, ℝ) × Set.Icc (0 : ℝ) 1 ↦
      z.1 z.2) := continuous_eval
  exact hc.measurable.comp (hψ.prodMk ht)

/-- The homogeneous perspective is measurable on measurable nonnegative coordinates,
including where both coordinates vanish. -/
theorem IsMeasurableFamily.perspective {Ω : Type*} [MeasurableSpace Ω]
    {ψ : Ω → NormShape} (hψ : IsMeasurableFamily ψ) {a b : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (ha0 : ∀ ω, 0 ≤ a ω) (hb0 : ∀ ω, 0 ≤ b ω) :
    Measurable (fun ω ↦ (ψ ω).perspective (a ω) (b ω)) := by
  have hr (ω : Ω) : a ω / (a ω + b ω) ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases hz : a ω + b ω = 0
    · simp [hz]
    · have hp : 0 < a ω + b ω := lt_of_le_of_ne (add_nonneg (ha0 ω) (hb0 ω)) (Ne.symm hz)
      exact ⟨div_nonneg (ha0 ω) hp.le, (div_le_one hp).mpr (by linarith [hb0 ω])⟩
  exact (ha.add hb).mul (hψ.eval ((ha.div (ha.add hb)).subtype_mk (h := hr)))

end ArakelovGeometry.NormShape

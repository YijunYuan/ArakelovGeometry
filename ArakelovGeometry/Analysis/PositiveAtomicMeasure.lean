/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Positive atoms on an arbitrary index space

No countability or sigma-finiteness is imposed on the original measure.
Integrable functions have countable support when every singleton has positive
mass: their norm-density measure is finite and has positive mass at each
point of the support.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Positive mass at every point turns almost-everywhere assertions into
pointwise assertions, without a countability hypothesis. -/
theorem ae_iff_forall_of_pos_singletons (hμ : ∀ x, 0 < μ {x}) (P : X → Prop) :
    (∀ᵐ x ∂μ, P x) ↔ ∀ x, P x := by
  constructor
  · intro h x
    by_contra hx
    have hs : ({x} : Set X) ⊆ {y | ¬ P y} := Set.singleton_subset_iff.mpr hx
    have hz : μ {x} ≤ μ {y | ¬ P y} := measure_mono hs
    rw [ae_iff.mp h] at hz
    exact (not_le_of_gt (hμ x)) hz
  · exact Filter.Eventually.of_forall

variable [MeasurableSingletonClass X]

/-- An integrable real function has countable actual support on any measure
with positive singleton masses, including uncountable discrete spaces. -/
theorem countable_support_of_integrable_of_pos_singletons
    (hμ : ∀ x, 0 < μ {x}) {f : X → ℝ} (hf : Integrable f μ) :
    (Function.support f).Countable := by
  let ν := μ.withDensity (fun x => ‖f x‖ₑ)
  let : IsFiniteMeasure ν :=
    isFiniteMeasure_withDensity hf.hasFiniteIntegral.ne
  have hc : Set.Countable {x | 0 < ν {x}} :=
    Measure.countable_meas_pos_of_disjoint_iUnion (μ := ν)
      (fun x => measurableSet_singleton x)
      (fun _ _ h => Set.disjoint_singleton.mpr h)
  refine hc.mono ?_
  intro x hx
  change 0 < μ.withDensity (fun y => ‖f y‖ₑ) {x}
  rw [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton]
  exact ENNReal.mul_pos_iff.mpr
    ⟨by simpa only [enorm_pos, Function.mem_support] using hx, hμ x⟩

end ArakelovGeometry

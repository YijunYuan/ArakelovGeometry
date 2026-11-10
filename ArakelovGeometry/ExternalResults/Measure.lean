/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Integration of functions with finite support

The integration criteria in this file apply to an arbitrary measurable space:
a function supported in a finite set whose points have finite measure is integrable
(`MeasureTheory.integrable_of_support_subset_finset`), and its Bochner integral is the
weighted sum of its values (`MeasureTheory.integral_eq_sum_of_support_subset_finset`).
Unlike the Dirac-sum criteria of `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure`, these
do not require the ambient space to be countable.
-/

@[expose] public section

namespace MeasureTheory

open scoped ENNReal

section FiniteSupport

variable {X E : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [NormedAddCommGroup E]
  {μ : Measure X} {g : X → E} {s : Finset X}

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- A function supported in a finite set is the sum of its one-point indicator pieces. -/
theorem eq_sum_indicator_of_support_subset (hsupp : Function.support g ⊆ s) :
    g = fun x ↦ ∑ x₀ ∈ s, ({x₀} : Set X).indicator (fun _ ↦ g x₀) x := by
  classical
  funext x
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Finset.sum_ite_eq]
  split_ifs with hx
  · rfl
  · exact Function.notMem_support.mp fun h ↦ hx (hsupp h)

/-- A function supported in a finite set whose points have finite measure is integrable.
In contrast to `MeasureTheory.integrable_sum_dirac`, the ambient space need not be
countable. -/
theorem integrable_of_support_subset_finset (hsupp : Function.support g ⊆ s)
    (hμ : ∀ x ∈ s, μ {x} ≠ ∞) : Integrable g μ := by
  rw [eq_sum_indicator_of_support_subset hsupp]
  refine integrable_finsetSum s fun x₀ hx₀ ↦ ?_
  rw [integrable_indicator_iff (measurableSet_singleton x₀)]
  exact integrableOn_const (hμ x₀ hx₀)

/-- The Bochner integral of a function supported in a finite set is the weighted sum of its
values. In contrast to `MeasureTheory.integral_sum_dirac_eq_tsum`, the ambient space need
not be countable. -/
theorem integral_eq_sum_of_support_subset_finset [NormedSpace ℝ E] [CompleteSpace E]
    (hsupp : Function.support g ⊆ s) (hμ : ∀ x ∈ s, μ {x} ≠ ∞) :
    ∫ x, g x ∂μ = ∑ x₀ ∈ s, (μ {x₀}).toReal • g x₀ := by
  conv_lhs => rw [eq_sum_indicator_of_support_subset hsupp]
  rw [integral_finsetSum s fun x₀ hx₀ ↦ (integrable_indicator_iff
    (measurableSet_singleton x₀)).mpr (integrableOn_const (hμ x₀ hx₀))]
  exact Finset.sum_congr rfl fun x₀ _ ↦ integral_indicator_const _ (measurableSet_singleton x₀)

end FiniteSupport

end MeasureTheory

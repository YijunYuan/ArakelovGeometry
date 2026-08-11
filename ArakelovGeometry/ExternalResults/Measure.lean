/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Measures prescribed on singletons

On a countable measurable space with measurable singletons, a measure is determined by its
values on singletons.  This file constructs the measure `MeasureTheory.Measure.ofSingletons f`
with prescribed values `f x` on each singleton `{x}` and proves its characteristic property
and uniqueness.

It also provides finite-support integration criteria valid over an *arbitrary* index space:
a function supported in a finite set whose points have finite measure is integrable
(`MeasureTheory.integrable_of_support_subset_finset`), and its Bochner integral is the
weighted sum of its values (`MeasureTheory.integral_eq_sum_of_support_subset_finset`).
Unlike the Dirac-sum criteria of `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure`, these
do not require the ambient space to be countable.
-/

namespace MeasureTheory

open scoped ENNReal

namespace Measure

variable {X : Type*} [MeasurableSpace X]

/-- The measure on a measurable space with prescribed values `f x` on each singleton `{x}`,
built as the sum of scaled Dirac measures `∑ x, f x • δ x`.

On a countable space with measurable singletons this is the unique measure with
`ofSingletons f {x} = f x` (see `ofSingletons_singleton` and `eq_ofSingletons`). -/
noncomputable def ofSingletons (f : X → ℝ≥0∞) : Measure X :=
  Measure.sum (fun a ↦ f a • Measure.dirac a)

variable [MeasurableSingletonClass X]

/-- `ofSingletons f` takes the prescribed value `f x` on the singleton `{x}`. -/
@[simp]
theorem ofSingletons_singleton (f : X → ℝ≥0∞) (x : X) : ofSingletons f {x} = f x :=
  Measure.sum_smul_dirac_singleton

variable [Countable X]

/-- On a countable space with measurable singletons, any measure agreeing with `f` on singletons
equals `ofSingletons f`. -/
theorem eq_ofSingletons {f : X → ℝ≥0∞} {μ : Measure X} (hμ : ∀ x, μ {x} = f x) :
    μ = ofSingletons f :=
  Measure.ext_of_singleton fun x ↦ by rw [hμ, ofSingletons_singleton]

/-- On a countable measurable space in which singletons are measurable, a measure is determined by
its values on singletons: for every `f : X → ℝ≥0∞` there is a unique measure `μ` with
`μ {x} = f x` for all `x`. -/
theorem existsUnique_singleton (f : X → ℝ≥0∞) : ∃! μ : Measure X, ∀ x, μ {x} = f x :=
  ⟨ofSingletons f, ofSingletons_singleton f, fun _ hν ↦ eq_ofSingletons hν⟩

end Measure

section FiniteSupport

variable {X E : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [NormedAddCommGroup E]
  {μ : Measure X} {g : X → E} {s : Finset X}

omit [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- A function supported in a finite set is the sum of its one-point indicator pieces. -/
theorem eq_sum_indicator_of_support_subset (hsupp : Function.support g ⊆ s) :
    g = fun x ↦ ∑ x₀ ∈ s, ({x₀} : Set X).indicator (fun _ ↦ g x₀) x := by
  classical
  funext x
  have key : ∀ x₀, ({x₀} : Set X).indicator (fun _ ↦ g x₀) x = if x₀ = x then g x₀ else 0 := by
    intro x₀
    by_cases h : x₀ = x
    · subst h
      rw [if_pos rfl, Set.indicator_of_mem (Set.mem_singleton x₀)]
    · rw [if_neg h, Set.indicator_of_notMem (by simpa using Ne.symm h)]
  simp_rw [key]
  rw [Finset.sum_ite_eq' s x (fun x₀ ↦ g x₀)]
  by_cases hx : x ∈ s
  · rw [if_pos hx]
  · rw [if_neg hx]
    exact Function.notMem_support.mp fun h ↦ hx (hsupp h)

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

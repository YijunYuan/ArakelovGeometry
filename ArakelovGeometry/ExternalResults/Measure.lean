/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Measures prescribed on singletons

On a countable measurable space with measurable singletons, a measure is determined by its
values on singletons.  This file constructs the measure `MeasureTheory.Measure.ofSingletons f`
with prescribed values `f x` on each singleton `{x}` and proves its characteristic property
and uniqueness.
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

end MeasureTheory

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Places of a field

A *place* of a field `K` is an equivalence class of absolute values `K → ℝ`.  This file
defines the type `AbsoluteValue.Place K` of places, the trivial place, and the archimedean /
nonarchimedean dichotomy on places (via the chosen representative `Quotient.out`).
-/

@[expose] public section

namespace AbsoluteValue

/-- A place of a field `K`: an equivalence class of absolute values `K → ℝ`. -/
def Place (K : Type u) [Field K] : Type u := Quotient (@AbsoluteValue.instSetoid K _ ℝ _ _)

open Classical in
/-- The trivial place of `K`, the class of the trivial absolute value. -/
noncomputable def trivialPlace (K : Type u) [Field K] : Place K :=
  Quotient.mk' .trivial

open Classical in
/-- The chosen representative of the trivial place is the trivial absolute value itself:
over a field, an absolute value equivalent to the trivial one equals it. -/
theorem trivialPlace_out_eq {K : Type u} [Field K] :
    (trivialPlace K).out = .trivial := by
  -- `Quotient.mk_out` gives `.out ≈ .trivial`; over a field, an absolute value
  -- equivalent to the trivial one *equals* the trivial one (rigidity), so the
  -- chosen representative is forced to be `.trivial` on the nose.
  rw [← isEquiv_trivial_iff_eq_trivial]
  exact Quotient.mk_out (s := AbsoluteValue.instSetoid) AbsoluteValue.trivial

/-- A place is *nonarchimedean* if its chosen representative is a nonarchimedean
absolute value. -/
def IsNonarchimedeanPlace {K : Type u} [Field K] (v : Place K) : Prop :=
  IsNonarchimedean v.out

open Classical in
/-- The trivial place is nonarchimedean. -/
theorem isNonarchimedeanPlace_trivialPlace {K : Type u} [Field K] :
    IsNonarchimedeanPlace (trivialPlace K) := by
  -- Reduce to `IsNonarchimedean .trivial`, i.e. `triv (a+b) ≤ max (triv a) (triv b)`.
  unfold IsNonarchimedeanPlace
  rw [trivialPlace_out_eq]
  intro a b
  by_cases ha : a = 0
  · -- a = 0: a + b = b, so `triv (a+b) = triv b ≤ max (triv 0) (triv b)`.
    subst ha
    simp only [zero_add]
    exact le_max_right _ _
  · -- a ≠ 0: `triv (a+b) ≤ 1 = triv a ≤ max (triv a) (triv b)`.
    have hbound : (AbsoluteValue.trivial : AbsoluteValue K ℝ) (a + b) ≤ 1 := by
      by_cases hab : a + b = 0
      · simp [hab]
      · rw [AbsoluteValue.trivial_apply hab]
    calc (AbsoluteValue.trivial : AbsoluteValue K ℝ) (a + b) ≤ 1 := hbound
      _ = AbsoluteValue.trivial a := (AbsoluteValue.trivial_apply ha).symm
      _ ≤ max (AbsoluteValue.trivial a) (AbsoluteValue.trivial b) := le_max_left _ _

/-- A place is *archimedean* if its chosen representative is not a nonarchimedean
absolute value. -/
def IsArchimedeanPlace {K : Type u} [Field K] (v : Place K) : Prop :=
  ¬IsNonarchimedean v.out

/-- Every place is nonarchimedean or archimedean. -/
theorem isNonarchimedeanPlace_or_isArchimedeanPlace {K : Type u} [Field K] (v : Place K) :
    IsNonarchimedeanPlace v ∨ IsArchimedeanPlace v := by
  simp [IsNonarchimedeanPlace, IsArchimedeanPlace, em]

end AbsoluteValue

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

namespace AbsoluteValue

def Place (K : Type u) [Field K] : Type u := Quotient (@AbsoluteValue.instSetoid K _ ℝ _ _)

open Classical in
noncomputable def TrivialPlace (K : Type u) [Field K] : Place K :=
  Quotient.mk' (.trivial)

open Classical in
theorem trivialPlace_out_eq {K : Type u} [Field K] :
  (TrivialPlace K).out = .trivial := by
  -- `Quotient.mk_out` gives `.out ≈ .trivial`; over a field, an absolute value
  -- equivalent to the trivial one *equals* the trivial one (rigidity), so the
  -- chosen representative is forced to be `.trivial` on the nose.
  rw [← isEquiv_trivial_iff_eq_trivial]
  exact Quotient.mk_out (s := AbsoluteValue.instSetoid) AbsoluteValue.trivial

def IsNonarchimedeanPlace {K : Type u} [Field K] (v : Place K) : Prop :=
  IsNonarchimedean v.out

open Classical in
theorem isNonarchimedeanPlace_of_trivialPlace {K : Type u} [Field K] :
  IsNonarchimedeanPlace (TrivialPlace K) := by
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

def IsArchimedeanPlace {K : Type u} [Field K] (v : Place K) : Prop :=
  ¬ IsNonarchimedean v.out

theorem place_classification {K : Type u} [Field K] (v : Place K) :
  IsNonarchimedeanPlace v ∨ IsArchimedeanPlace v := by
  simp [IsNonarchimedeanPlace, IsArchimedeanPlace, em]


end AbsoluteValue

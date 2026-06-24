import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

namespace AbsoluteValue

def Place (K : Type u) [Field K] : Type u := Quotient (@AbsoluteValue.instSetoid K _ ℝ _ _)

open Classical in
noncomputable def TrivialPlace (K : Type u) [Field K] : Place K :=
  Quotient.mk' (.trivial)

open Classical in
theorem trivialPlace_out_eq {K : Type u} [Field K] :
  (TrivialPlace K).out = .trivial := by
  sorry

def IsNonarchimedeanPlace {K : Type u} [Field K] (v : Place K) : Prop :=
  IsNonarchimedean v.out

theorem isNonarchimedeanPlace_of_trivialPlace {K : Type u} [Field K] :
  IsNonarchimedeanPlace (TrivialPlace K) := by
  sorry

def IsArchimedeanPlace {K : Type u} [Field K] (v : Place K) : Prop :=
  ¬ IsNonarchimedean v.out

theorem place_classification {K : Type u} [Field K] (v : Place K) :
  IsNonarchimedeanPlace v ∨ IsArchimedeanPlace v := by
  simp [IsNonarchimedeanPlace, IsArchimedeanPlace, em]


end AbsoluteValue

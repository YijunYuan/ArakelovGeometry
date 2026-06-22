import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

abbrev PlaceSetoid (K : Type*) [Field K] : Setoid (AbsoluteValue K ℝ) where
  r v w:= v.IsEquiv w
  iseqv := { refl := fun _ =>
    AbsoluteValue.IsEquiv.rfl, symm :=
    AbsoluteValue.IsEquiv.symm , trans :=
    AbsoluteValue.IsEquiv.trans }

def Place (K : Type u) [Field K] : Type u := Quotient (PlaceSetoid K)

def IsFinitePlace {K : Type u} [Field K] (v : Place K) : Prop := IsNonarchimedean v.out

def IsInfinitePlace {K : Type u} [Field K] (v : Place K) : Prop := ¬ IsFinitePlace v

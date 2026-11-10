/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Amalgamation
public import ArakelovGeometry.AdelicCurve.Examples.RationalFunction.Archimedean
public import ArakelovGeometry.AdelicCurve.Examples.RationalFunction.FinitePlaces

/-!
# The rational-function adelic curve and the augmented rational curve

This assembles the actual three components of Chen–Moriwaki §3.2.5 and
Example 3.7.2(3). The horizontal parameter space is the closed points of `𝔸¹_ℚ`,
as specified in §3.2.5; the later example's reference to all closed points of
`ℙ¹_ℚ` omits the exclusion of infinity.

The target model groups the source's amalgamation as
`(HorizontalPlace ⊕ Nat.Primes) ⊕ Unit`. Its finite absolute values are
restrictions along `ℚ → ℚ(T)`, identified below with trivial and `p`-adic values.
The final point has mass one and carries the usual real absolute value.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicCurve.RationalFunction

open MeasureTheory

/-- The horizontal and vertical finite components, with counting measure on each. -/
noncomputable def finiteAdelicStructure : AdelicStructure (RatFunc ℚ) :=
  horizontalAdelicStructure.amalgamation primeAdelicStructure

/-- The actual adelic structure on `ℚ(T)` from Chen–Moriwaki §3.2.5. -/
noncomputable def adelicStructure : AdelicStructure (RatFunc ℚ) :=
  finiteAdelicStructure.amalgamation archimedeanAdelicStructure

/-- The rational-function adelic curve occurring in Example 3.7.2(3). -/
noncomputable abbrev adelicCurve : AdelicCurve := adelicStructure.toAdelicCurve

/-- The restrictions to `ℚ` of the finite components of the rational-function curve. -/
noncomputable def rationalFiniteAdelicStructure : AdelicStructure ℚ where
  Ω := finiteAdelicStructure.Ω
  A := finiteAdelicStructure.A
  v := finiteAdelicStructure.v
  ϕ ω := (finiteAdelicStructure.ϕ ω).pullback (algebraMap ℚ (RatFunc ℚ))
  measurable_log a ha := finiteAdelicStructure.measurable_log
    (algebraMap ℚ (RatFunc ℚ) a) ((map_ne_zero _).mpr ha)
  integrable_log a ha := finiteAdelicStructure.integrable_log
    (algebraMap ℚ (RatFunc ℚ) a) ((map_ne_zero _).mpr ha)

/-- The ordinary infinite place of `ℚ`, on a singleton of mass one. -/
noncomputable def rationalInfiniteAdelicStructure : AdelicStructure ℚ where
  Ω := Unit
  v := Measure.dirac ()
  ϕ _ := Rat.AbsoluteValue.real
  measurable_log _ _ := measurable_const
  integrable_log _ _ := integrable_const _

/-- The rational adelic curve augmented by the source's horizontal trivial places. -/
noncomputable def augmentedRationalAdelicStructure : AdelicStructure ℚ :=
  rationalFiniteAdelicStructure.amalgamation rationalInfiniteAdelicStructure

/-- The target adelic curve of Example 3.7.2(3). -/
noncomputable abbrev augmentedRationalAdelicCurve : AdelicCurve :=
  augmentedRationalAdelicStructure.toAdelicCurve

@[simp]
theorem adelicStructure_horizontal (v : HorizontalPlace) (f : RatFunc ℚ) :
    adelicStructure.ϕ (Sum.inl (Sum.inl v)) f = horizontalAbv v f := rfl

@[simp]
theorem adelicStructure_prime (p : Nat.Primes) (f : RatFunc ℚ) :
    adelicStructure.ϕ (Sum.inl (Sum.inr p)) f = primeAbv p f := rfl

@[simp]
theorem adelicStructure_archimedean (t : ArchimedeanPlace) (f : RatFunc ℚ) :
    adelicStructure.ϕ (Sum.inr t) f = archimedeanAbv t f := rfl

@[simp]
theorem augmentedRationalAdelicStructure_horizontal (v : HorizontalPlace) (a : ℚ) :
    augmentedRationalAdelicStructure.ϕ (Sum.inl (Sum.inl v)) a =
      (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ) a :=
  horizontalAbv_rat v a

@[simp]
theorem augmentedRationalAdelicStructure_prime (p : Nat.Primes) (a : ℚ) :
    augmentedRationalAdelicStructure.ϕ (Sum.inl (Sum.inr p)) a = rationalPadicAbv p a :=
  primeAbv_rat p a

@[simp]
theorem augmentedRationalAdelicStructure_infinite (a : ℚ) :
    augmentedRationalAdelicStructure.ϕ (Sum.inr ()) a = Rat.AbsoluteValue.real a := rfl

/-- The source's measure is the sum of its finite and archimedean component measures. -/
theorem adelicStructure_measure :
    adelicStructure.v = finiteAdelicStructure.v.map Sum.inl +
      archimedeanMeasure.map (@Sum.inr finiteAdelicStructure.Ω ArchimedeanPlace) := rfl

/-- The augmented target has the same finite measure and a point of mass one. -/
theorem augmentedRationalAdelicStructure_measure :
    augmentedRationalAdelicStructure.v = finiteAdelicStructure.v.map Sum.inl +
      (Measure.dirac ()).map (@Sum.inr finiteAdelicStructure.Ω Unit) := rfl

end ArakelovGeometry.AdelicCurve.RationalFunction

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.AlgebraicClosure
import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Completion

/-!
# Regression checks for canonical typeclass inference

The number-field metric must preserve the original distance and pseudometric,
and relative algebraic closures must inherit countability without a local instance.
-/

open ArakelovGeometry ArakelovGeometry.AdelicStructure
open ArakelovGeometry.StronglyDominatedNormFamily

noncomputable section

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

example : T0Space (StronglyDominatedNormFamily (normalizedNumberFieldAdelicStructure K) E) :=
  inferInstance

example : MetricSpace (StronglyDominatedNormFamily (normalizedNumberFieldAdelicStructure K) E) :=
  inferInstance

example : CompleteSpace (StronglyDominatedNormFamily (normalizedNumberFieldAdelicStructure K) E) :=
  inferInstance

example : (numberFieldMetricSpace (K := K) (E := E)).toPseudoMetricSpace =
    instPseudoMetricSpace (S := normalizedNumberFieldAdelicStructure K) (E := E) := rfl

example (ξ η : StronglyDominatedNormFamily (normalizedNumberFieldAdelicStructure K) E) :
    dist ξ η = (ξ.val.upperIntegralDist η.val).toReal := rfl

example {L : Type*} [Field L] [Algebra K L] (K₀ : Subfield K) [Countable K₀] :
    Countable (algebraicClosure K₀ L).toSubfield := inferInstance

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Subquotient
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic

import ArakelovGeometry.AdelicVectorBundle.Measurability.Countable
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Automatic adelic subquotients and duals

The exact alternatives in Remark 4.1.34 discharge the measurability premises
of the existing bundle constructors: a discrete parameter sigma-algebra, or
one countable subfield dense in every completion. No assertion about the
parameter space of an algebraic scalar extension is used.
-/

@[expose] public section

namespace ArakelovGeometry

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

namespace NormFamily

/-- The two source alternatives give actual dual measurability. -/
theorem IsMeasurable.dual_of_discrete_or_countable {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable)
    [hS : S.NormMeasurabilityHypotheses] :
    ξ.dual.IsMeasurable := by
  rcases hS.discrete_or_countable with hS | hS
  · let := hS
    exact ξ.dual.isMeasurable_of_discrete
  · exact hξ.dual_of_common_countable_dense_subfield hS

/-- The same source alternatives give actual quotient measurability. -/
theorem IsMeasurable.pushforward_of_discrete_or_countable {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable)
    [hS : S.NormMeasurabilityHypotheses]
    (f : E →ₗ[K] F) (hf : Function.Surjective f) :
    (ξ.pushforward f hf).IsMeasurable := by
  rcases hS.discrete_or_countable with hS | hS
  · let := hS
    exact (ξ.pushforward f hf).isMeasurable_of_discrete
  · exact hξ.pushforward_of_common_countable_dense_subfield f hf hS

/-- Measurability of local distance under the two alternatives on the original base. -/
theorem IsMeasurable.localDist_of_discrete_or_countable {ξ η : NormFamily S E}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    [hS : S.NormMeasurabilityHypotheses] :
    Measurable (ξ.localDist η) := by
  rcases hS.discrete_or_countable with hS | hS
  · let := hS
    exact Measurable.of_discrete
  · exact hξ.localDist_of_common_countable_dense_subfield hη hS

instance instIsMeasurableDual (ξ : NormFamily S E) [ξ.IsMeasurable]
    [S.NormMeasurabilityHypotheses] : ξ.dual.IsMeasurable :=
  IsMeasurable.dual_of_discrete_or_countable inferInstance

instance instIsMeasurablePushforward (ξ : NormFamily S E) [ξ.IsMeasurable]
    [S.NormMeasurabilityHypotheses] (f : E →ₗ[K] F) (hf : Function.Surjective f) :
    (ξ.pushforward f hf).IsMeasurable :=
  IsMeasurable.pushforward_of_discrete_or_countable inferInstance f hf

instance instIsMeasurableQuotient (ξ : NormFamily S E) [ξ.IsMeasurable]
    [S.NormMeasurabilityHypotheses] (P : Submodule K E) : (ξ.quotient P).IsMeasurable :=
  instIsMeasurablePushforward ξ P.mkQ P.mkQ_surjective

end NormFamily

namespace AdelicVectorBundle

/-- A dominated measurable norm family is adelic under either source base hypothesis;
dual measurability is proved by the countable norm formula or discreteness. -/
abbrev ofMeasurableDominated (ξ : NormFamily S E) [hm : ξ.IsMeasurable]
    [hd : ξ.IsDominated]
    [hS : S.NormMeasurabilityHypotheses] :
    AdelicVectorBundle S where
  carrier := E
  toNormFamily := ξ
  toIsAdelic := {
    isMeasurable := hm
    dual_isMeasurable := hm.dual_of_discrete_or_countable
    isDominated := hd
  }

@[simp]
theorem ofMeasurableDominated_toNormFamily (ξ : NormFamily S E) [hm : ξ.IsMeasurable]
    [hd : ξ.IsDominated]
    [hS : S.NormMeasurabilityHypotheses] :
    (ofMeasurableDominated ξ).toNormFamily = ξ := rfl

/-- Automatic dual bundle, using the established canonical dual constructor. -/
noncomputable abbrev dualOfNormMeasurability (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses] :
    AdelicVectorBundle S :=
  V.dual (hm := (V.dual_isMeasurable.dual_of_discrete_or_countable))

@[simp]
theorem dualOfNormMeasurability_toNormFamily (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses] :
    (V.dualOfNormMeasurability).toNormFamily = V.toNormFamily.dual := rfl

theorem dualOfNormMeasurability_isStronglyAdelic (V : AdelicVectorBundle S)
    [S.NormMeasurabilityHypotheses] :
    (V.dualOfNormMeasurability).IsStronglyAdelic := V.isDominated.strong_dual

/-- Automatic rational subbundle with the actual completed restriction norm. -/
noncomputable abbrev restrictOfNormMeasurability (V : AdelicVectorBundle S) (F : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses] :
    AdelicVectorBundle S :=
  V.restrict F (hm := ((V.isMeasurable.restrict F).dual_of_discrete_or_countable))

@[simp]
theorem restrictOfNormMeasurability_toNormFamily (V : AdelicVectorBundle S)
    (F : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses] :
    (V.restrictOfNormMeasurability F).toNormFamily = V.toNormFamily.restrict F := rfl

/-- Automatic rational quotient bundle with the actual completed quotient norm. -/
noncomputable abbrev quotientOfNormMeasurability (V : AdelicVectorBundle S) (F : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses] :
    AdelicVectorBundle S :=
  V.quotient F (hm := (V.isMeasurable.pushforward_of_discrete_or_countable
    F.mkQ F.mkQ_surjective))

@[simp]
theorem quotientOfNormMeasurability_toNormFamily (V : AdelicVectorBundle S)
    (F : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses] :
    (V.quotientOfNormMeasurability F).toNormFamily = V.toNormFamily.quotient F := rfl

/-- Strong adelicity descends to the automatic rational subbundle. -/
theorem IsStronglyAdelic.restrictOfNormMeasurability {V : AdelicVectorBundle S}
    (hV : V.IsStronglyAdelic) (F : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.restrictOfNormMeasurability F).IsStronglyAdelic :=
  hV.restrict F _

/-- Strong adelicity descends to the automatic rational quotient. -/
theorem IsStronglyAdelic.quotientOfNormMeasurability {V : AdelicVectorBundle S}
    (hV : V.IsStronglyAdelic) (F : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.quotientOfNormMeasurability F).IsStronglyAdelic :=
  hV.quotient F _

instance instIsHermitianRestrictOfNormMeasurability (V : AdelicVectorBundle S)
    [S.NormMeasurabilityHypotheses] [S.IsArchimedeanNormalized] [hV : V.IsHermitian]
    (P : Submodule K V) : (V.restrictOfNormMeasurability P).IsHermitian :=
  NormFamily.IsHermitian.restrict hV P

instance instIsHermitianQuotientOfNormMeasurability (V : AdelicVectorBundle S)
    [S.NormMeasurabilityHypotheses] [S.IsArchimedeanNormalized] [hV : V.IsHermitian]
    (P : Submodule K V) : (V.quotientOfNormMeasurability P).IsHermitian :=
  NormFamily.IsHermitian.quotient hV P

instance instIsHermitianDualOfNormMeasurability (V : AdelicVectorBundle S)
    [S.NormMeasurabilityHypotheses] [S.IsArchimedeanNormalized] [hV : V.IsHermitian] :
    V.dualOfNormMeasurability.IsHermitian :=
  NormFamily.IsHermitian.dual hV

instance instIsStronglyAdelicRestrictOfNormMeasurability (V : AdelicVectorBundle S)
    [S.NormMeasurabilityHypotheses] [S.IsArchimedeanNormalized] [hV : V.IsStronglyAdelic]
    (P : Submodule K V) : (V.restrictOfNormMeasurability P).IsStronglyAdelic :=
  IsStronglyAdelic.restrictOfNormMeasurability hV P

instance instIsStronglyAdelicQuotientOfNormMeasurability (V : AdelicVectorBundle S)
    [S.NormMeasurabilityHypotheses] [S.IsArchimedeanNormalized] [hV : V.IsStronglyAdelic]
    (P : Submodule K V) : (V.quotientOfNormMeasurability P).IsStronglyAdelic :=
  IsStronglyAdelic.quotientOfNormMeasurability hV P

end AdelicVectorBundle

end ArakelovGeometry

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
    [hS : S.HasMeasurableBase] :
    ξ.dual.IsMeasurable := by
  rcases hS.discrete_or_countable with hS | hS
  · let := hS
    exact ξ.dual.isMeasurable_of_discrete
  · exact hξ.dual_of_common_countable_dense_subfield hS

/-- The same source alternatives give actual quotient measurability. -/
theorem IsMeasurable.pushforward_of_discrete_or_countable {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable)
    [hS : S.HasMeasurableBase]
    (f : E →ₗ[K] F) (hf : Function.Surjective f) :
    (ξ.pushforward f hf).IsMeasurable := by
  rcases hS.discrete_or_countable with hS | hS
  · let := hS
    exact (ξ.pushforward f hf).isMeasurable_of_discrete
  · exact hξ.pushforward_of_common_countable_dense_subfield f hf hS

/-- Measurability of local distance under the two alternatives on the original base. -/
theorem IsMeasurable.localDist_of_discrete_or_countable {ξ η : NormFamily S E}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    [hS : S.HasMeasurableBase] :
    Measurable (ξ.localDist η) := by
  rcases hS.discrete_or_countable with hS | hS
  · let := hS
    exact Measurable.of_discrete
  · exact hξ.localDist_of_common_countable_dense_subfield hη hS

instance instIsMeasurableDual (ξ : NormFamily S E) [ξ.IsMeasurable]
    [S.HasMeasurableBase] : ξ.dual.IsMeasurable :=
  IsMeasurable.dual_of_discrete_or_countable inferInstance

instance instIsMeasurablePushforward (ξ : NormFamily S E) [ξ.IsMeasurable]
    [S.HasMeasurableBase] (f : E →ₗ[K] F) (hf : Function.Surjective f) :
    (ξ.pushforward f hf).IsMeasurable :=
  IsMeasurable.pushforward_of_discrete_or_countable inferInstance f hf

instance instIsMeasurableQuotient (ξ : NormFamily S E) [ξ.IsMeasurable]
    [S.HasMeasurableBase] (P : Submodule K E) : (ξ.quotient P).IsMeasurable :=
  instIsMeasurablePushforward ξ P.mkQ P.mkQ_surjective

end NormFamily

namespace AdelicVectorBundle

/-- A dominated measurable norm family is adelic under either source base hypothesis;
dual measurability is proved by the countable norm formula or discreteness. -/
abbrev ofMeasurableDominated (ξ : NormFamily S E) [hm : ξ.IsMeasurable]
    [hd : ξ.IsDominated]
    [hS : S.HasMeasurableBase] :
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
    [hS : S.HasMeasurableBase] :
    (ofMeasurableDominated ξ).toNormFamily = ξ := rfl

/-- Automatic dual bundle, using the established canonical dual constructor. -/
noncomputable abbrev dualOfMeasurableBase (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase] :
    AdelicVectorBundle S :=
  V.dual (hm := (V.dual_isMeasurable.dual_of_discrete_or_countable))

@[simp]
theorem dualOfMeasurableBase_toNormFamily (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase] :
    (V.dualOfMeasurableBase).toNormFamily = V.toNormFamily.dual := rfl

theorem dualOfMeasurableBase_isStronglyAdelic (V : AdelicVectorBundle S)
    [S.HasMeasurableBase] :
    (V.dualOfMeasurableBase).IsStronglyAdelic := V.isDominated.strong_dual

/-- Automatic rational subbundle with the actual completed restriction norm. -/
noncomputable abbrev restrictOfMeasurableBase (V : AdelicVectorBundle S) (F : Submodule K V)
    [hS : S.HasMeasurableBase] :
    AdelicVectorBundle S :=
  V.restrict F (hm := ((V.isMeasurable.restrict F).dual_of_discrete_or_countable))

@[simp]
theorem restrictOfMeasurableBase_toNormFamily (V : AdelicVectorBundle S)
    (F : Submodule K V)
    [hS : S.HasMeasurableBase] :
    (V.restrictOfMeasurableBase F).toNormFamily = V.toNormFamily.restrict F := rfl

/-- Automatic rational quotient bundle with the actual completed quotient norm. -/
noncomputable abbrev quotientOfMeasurableBase (V : AdelicVectorBundle S) (F : Submodule K V)
    [hS : S.HasMeasurableBase] :
    AdelicVectorBundle S :=
  V.quotient F (hm := (V.isMeasurable.pushforward_of_discrete_or_countable
    F.mkQ F.mkQ_surjective))

@[simp]
theorem quotientOfMeasurableBase_toNormFamily (V : AdelicVectorBundle S)
    (F : Submodule K V)
    [hS : S.HasMeasurableBase] :
    (V.quotientOfMeasurableBase F).toNormFamily = V.toNormFamily.quotient F := rfl

/-- Strong adelicity descends to the automatic rational subbundle. -/
theorem IsStronglyAdelic.restrictOfMeasurableBase {V : AdelicVectorBundle S}
    (hV : V.IsStronglyAdelic) (F : Submodule K V)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.restrictOfMeasurableBase F).IsStronglyAdelic :=
  hV.restrict F _

/-- Strong adelicity descends to the automatic rational quotient. -/
theorem IsStronglyAdelic.quotientOfMeasurableBase {V : AdelicVectorBundle S}
    (hV : V.IsStronglyAdelic) (F : Submodule K V)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.quotientOfMeasurableBase F).IsStronglyAdelic :=
  hV.quotient F _

instance instIsHermitianRestrictOfMeasurableBase (V : AdelicVectorBundle S)
    [S.HasMeasurableBase] [S.IsArchimedeanNormalized] [hV : V.IsHermitian]
    (P : Submodule K V) : (V.restrictOfMeasurableBase P).IsHermitian :=
  NormFamily.IsHermitian.restrict hV P

instance instIsHermitianQuotientOfMeasurableBase (V : AdelicVectorBundle S)
    [S.HasMeasurableBase] [S.IsArchimedeanNormalized] [hV : V.IsHermitian]
    (P : Submodule K V) : (V.quotientOfMeasurableBase P).IsHermitian :=
  NormFamily.IsHermitian.quotient hV P

instance instIsHermitianDualOfMeasurableBase (V : AdelicVectorBundle S)
    [S.HasMeasurableBase] [S.IsArchimedeanNormalized] [hV : V.IsHermitian] :
    V.dualOfMeasurableBase.IsHermitian :=
  NormFamily.IsHermitian.dual hV

instance instIsStronglyAdelicRestrictOfMeasurableBase (V : AdelicVectorBundle S)
    [S.HasMeasurableBase] [S.IsArchimedeanNormalized] [hV : V.IsStronglyAdelic]
    (P : Submodule K V) : (V.restrictOfMeasurableBase P).IsStronglyAdelic :=
  IsStronglyAdelic.restrictOfMeasurableBase hV P

instance instIsStronglyAdelicQuotientOfMeasurableBase (V : AdelicVectorBundle S)
    [S.HasMeasurableBase] [S.IsArchimedeanNormalized] [hV : V.IsStronglyAdelic]
    (P : Submodule K V) : (V.quotientOfMeasurableBase P).IsStronglyAdelic :=
  IsStronglyAdelic.quotientOfMeasurableBase hV P

end AdelicVectorBundle

end ArakelovGeometry

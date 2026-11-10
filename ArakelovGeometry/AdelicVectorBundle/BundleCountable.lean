/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.BundleSubquotient
public import ArakelovGeometry.AdelicVectorBundle.CountableMeasurable

/-!
# Automatic adelic subquotients and duals

The exact alternatives in Remark 4.1.34 discharge the measurability premises
of the existing bundle constructors: a discrete parameter sigma-algebra, or
one countable subfield dense in every completion. No assertion about the
parameter space of an algebraic scalar extension is used.
-/

@[expose] public section

namespace ArakelovGeometry

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

namespace NormFamily

/-- The two source alternatives give actual dual measurability. -/
theorem IsMeasurable.dual_of_discrete_or_countable {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    ξ.dual.IsMeasurable := by
  rcases hS with hS | hS
  · let := hS
    exact ξ.dual.isMeasurable_of_discrete
  · exact hξ.dual_of_common_countable_dense_subfield hS

/-- The same source alternatives give actual quotient measurability. -/
theorem IsMeasurable.pushforward_of_discrete_or_countable {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (f : E →ₗ[K] F) (hf : Function.Surjective f) :
    (ξ.pushforward f hf).IsMeasurable := by
  rcases hS with hS | hS
  · let := hS
    exact (ξ.pushforward f hf).isMeasurable_of_discrete
  · exact hξ.pushforward_of_common_countable_dense_subfield f hf hS

/-- Measurability of local distance under the two alternatives on the original base. -/
theorem IsMeasurable.localDist_of_discrete_or_countable {ξ η : NormFamily S E}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    Measurable (ξ.localDist η) := by
  rcases hS with hS | hS
  · let := hS
    exact Measurable.of_discrete
  · exact hξ.localDist_of_common_countable_dense_subfield hη hS

end NormFamily

namespace AdelicVectorBundle

/-- A dominated measurable norm family is adelic under either source base hypothesis;
dual measurability is proved by the countable norm formula or discreteness. -/
def ofMeasurableDominated (ξ : NormFamily S E) (hm : ξ.IsMeasurable)
    (hd : ξ.IsDominated)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    AdelicVectorBundle S E where
  toNormFamily := ξ
  isMeasurable := hm
  dual_isMeasurable := hm.dual_of_discrete_or_countable hS
  isDominated := hd

@[simp]
theorem ofMeasurableDominated_toNormFamily (ξ : NormFamily S E) (hm : ξ.IsMeasurable)
    (hd : ξ.IsDominated)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (ofMeasurableDominated ξ hm hd hS).toNormFamily = ξ := rfl

/-- Automatic dual bundle, using the established canonical dual constructor. -/
noncomputable def dualOfMeasurableBase (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    AdelicVectorBundle S (Module.Dual K E) :=
  V.dual (V.dual_isMeasurable.dual_of_discrete_or_countable hS)

@[simp]
theorem dualOfMeasurableBase_toNormFamily (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (V.dualOfMeasurableBase hS).toNormFamily = V.toNormFamily.dual := rfl

theorem dualOfMeasurableBase_isStronglyAdelic (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (V.dualOfMeasurableBase hS).IsStronglyAdelic := V.isDominated.strong_dual

/-- Automatic rational subbundle with the actual completed restriction norm. -/
noncomputable def restrictOfMeasurableBase (V : AdelicVectorBundle S E) (F : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    AdelicVectorBundle S F :=
  V.restrict F ((V.isMeasurable.restrict F).dual_of_discrete_or_countable hS)

@[simp]
theorem restrictOfMeasurableBase_toNormFamily (V : AdelicVectorBundle S E)
    (F : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (V.restrictOfMeasurableBase F hS).toNormFamily = V.toNormFamily.restrict F := rfl

/-- Automatic rational quotient bundle with the actual completed quotient norm. -/
noncomputable def quotientOfMeasurableBase (V : AdelicVectorBundle S E) (F : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    AdelicVectorBundle S (E ⧸ F) :=
  V.quotient F (V.isMeasurable.pushforward_of_discrete_or_countable hS
    F.mkQ F.mkQ_surjective)

@[simp]
theorem quotientOfMeasurableBase_toNormFamily (V : AdelicVectorBundle S E)
    (F : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (V.quotientOfMeasurableBase F hS).toNormFamily = V.toNormFamily.quotient F := rfl

/-- Strong adelicity descends to the automatic rational subbundle. -/
theorem IsStronglyAdelic.restrictOfMeasurableBase {V : AdelicVectorBundle S E}
    (hV : V.IsStronglyAdelic) (F : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.restrictOfMeasurableBase F hS).IsStronglyAdelic :=
  hV.restrict F _ hN

/-- Strong adelicity descends to the automatic rational quotient. -/
theorem IsStronglyAdelic.quotientOfMeasurableBase {V : AdelicVectorBundle S E}
    (hV : V.IsStronglyAdelic) (F : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.quotientOfMeasurableBase F hS).IsStronglyAdelic :=
  hV.quotient F _ hN

end AdelicVectorBundle

end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.NumberTheory.NormFamilyNormalizedGlobalFiniteGeneration
public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldNormalizationDual

/-!
# Actual normalized number-field adelic bundles

The completed norm transport and dual comparison produce all the adelic-bundle
properties. Its dominated global finite-place ball is finitely generated.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

open AdelicStructure

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

variable (V : AdelicVectorBundle (numberFieldAdelicStructure K) E)
variable (hV : V.toNormFamily.IsUltrametric)

/-- The actual completed normalization, with domination and both measurability
clauses proved for the new family. -/
noncomputable def numberFieldNormalize :
    AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E := by
  let normalizedDiscrete : DiscreteMeasurableSpace (normalizedNumberFieldAdelicStructure K).Ω :=
    inferInstanceAs
      (DiscreteMeasurableSpace {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  exact {
    toNormFamily := V.toNormFamily.numberFieldNormalize hV
    isMeasurable := (V.toNormFamily.numberFieldNormalize hV).isMeasurable_of_discrete
    dual_isMeasurable := (V.toNormFamily.numberFieldNormalize hV).dual.isMeasurable_of_discrete
    isDominated := V.isDominated.numberFieldNormalize hV }

/-- The bundle uses the canonical actual normalized completed norm family. -/
theorem numberFieldNormalize_toNormFamily :
    (V.numberFieldNormalize hV).toNormFamily = V.toNormFamily.numberFieldNormalize hV := rfl

/-- The actual finite norm family of the normalized bundle is ultrametric. -/
theorem numberFieldNormalize_isUltrametric :
    (V.numberFieldNormalize hV).toNormFamily.IsUltrametric :=
  V.toNormFamily.numberFieldNormalize_isUltrametric hV

/-- The underlying rational dimension, including rank zero, is retained. -/
theorem numberFieldNormalize_rank : (V.numberFieldNormalize hV).rank = V.rank := rfl

/-- The genuine all-rank global finite-place unit ball is finitely generated
without a coherence assumption. -/
theorem numberFieldNormalize_fg_globalUnitBallModule :
    ((V.numberFieldNormalize hV).toNormFamily.globalUnitBallModule
      (V.numberFieldNormalize_isUltrametric hV)).FG :=
  (V.numberFieldNormalize hV).isDominated.fg_normalizedGlobalUnitBallModule
    (V.numberFieldNormalize_isUltrametric hV)

end ArakelovGeometry.AdelicVectorBundle

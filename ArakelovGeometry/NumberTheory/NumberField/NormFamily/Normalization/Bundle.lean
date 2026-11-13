/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.UnitBall.Global
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Basic

import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.FiniteGeneration
import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Dual

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

variable (V : AdelicVectorBundle (numberFieldAdelicStructure K))
variable [hV : V.toNormFamily.IsUltrametric]

/-- The actual completed normalization, with domination and both measurability
clauses proved for the new family. -/
noncomputable abbrev numberFieldNormalize :
    AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) where
  carrier := V
  toNormFamily := V.toNormFamily.numberFieldNormalize
  toIsAdelic := {
    isMeasurable := (V.toNormFamily.numberFieldNormalize).isMeasurable_of_discrete
    dual_isMeasurable := (V.toNormFamily.numberFieldNormalize).dual.isMeasurable_of_discrete
    isDominated := by exact V.isDominated.numberFieldNormalize hV
  }

/-- The bundle uses the canonical actual normalized completed norm family. -/
theorem numberFieldNormalize_toNormFamily :
    (V.numberFieldNormalize).toNormFamily = V.toNormFamily.numberFieldNormalize := rfl

/-- The actual finite norm family of the normalized bundle is ultrametric. -/
theorem numberFieldNormalize_isUltrametric :
    (V.numberFieldNormalize).toNormFamily.IsUltrametric :=
  V.toNormFamily.numberFieldNormalize_isUltrametric

/-- The underlying rational dimension, including rank zero, is retained. -/
theorem numberFieldNormalize_rank : (V.numberFieldNormalize).rank = V.rank := rfl

/-- The genuine all-rank global finite-place unit ball is finitely generated
without a coherence assumption. -/
theorem numberFieldNormalize_fg_globalUnitBallModule :
    ((V.numberFieldNormalize).toNormFamily.globalUnitBallModule
      (hξ := (V.numberFieldNormalize_isUltrametric))).FG :=
  (V.numberFieldNormalize).isDominated.fg_normalizedGlobalUnitBallModule
    (V.numberFieldNormalize_isUltrametric)

end ArakelovGeometry.AdelicVectorBundle

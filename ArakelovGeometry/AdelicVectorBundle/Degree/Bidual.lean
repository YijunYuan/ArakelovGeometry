/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic

import ArakelovGeometry.AdelicVectorBundle.Determinant.Bidual
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Bidual invariance of Arakelov degree

The canonical bidual adelic bundle uses the established dual and pullback
constructors and the evaluation map on the original vector space. The actual
completed determinant equality proves source equation(4.23), also in rank zero.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.AdelicVectorBundle

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual bidual family on the original rational space, with its
measurability supplied by the exact base alternatives. -/
noncomputable abbrev bidualOfNormMeasurability (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses] :
    AdelicVectorBundle S :=
  ((V.dualOfNormMeasurability).dualOfNormMeasurability).pullback
    (Module.Dual.eval K V) (Module.eval_apply_injective K) (hm := (by
      change (V.toNormFamily.dual.dual.pullback (Module.Dual.eval K V)
        (Module.eval_apply_injective K)).dual.IsMeasurable
      rw [V.toNormFamily.dual_dual_pullback_dual_eq]
      exact V.dual_isMeasurable))

@[simp]
theorem bidualOfNormMeasurability_toNormFamily (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses] :
    (V.bidualOfNormMeasurability).toNormFamily =
      V.toNormFamily.dual.dual.pullback (Module.Dual.eval K V)
        (Module.eval_apply_injective K) := rfl

/-- The canonical bidual of any adelic bundle is strongly adelic. -/
theorem bidualOfNormMeasurability_isStronglyAdelic (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.bidualOfNormMeasurability).IsStronglyAdelic :=
  ((V.dualOfNormMeasurability).dualOfNormMeasurability_isStronglyAdelic).pullback
    (Module.Dual.eval K V) (Module.eval_apply_injective K) _

/-- Source equation(4.23), proved by equality of the actual completed
projective determinant norms, with no ultrametricity assumption on the original. -/
theorem degree_bidualOfNormMeasurability [S.IsProper] (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.bidualOfNormMeasurability).degree = V.degree := by
  let s := (V.determinantOfNormMeasurability).lineGenerator
    (hV := (V.determinantOfNormMeasurability_isLine))
  rw [(V.bidualOfNormMeasurability).degree_eq_neg_integral s,
    V.degree_eq_neg_integral s, bidualOfNormMeasurability_toNormFamily,
    V.toNormFamily.determinant_dual_dual_pullback]

end ArakelovGeometry.AdelicVectorBundle

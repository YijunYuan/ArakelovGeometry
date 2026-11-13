/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Majorant.ExactSequence
import ArakelovGeometry.MeasureTheory.Integral.UpperEnvelope
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Global majorant discrepancy in an exact sequence

The local elementary-majorant infimum bounds the genuine global lower
integrals of the restricted and quotient bundles. No measurability of the
local infimum or finiteness of the global discrepancy is assumed.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.AdelicVectorBundle

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The two end lower integrals sum to at most the middle lower integral,
also when one or more of these genuine global discrepancies are infinite. -/
theorem majorantDiscrepancy_restrict_add_quotient_le (V : AdelicVectorBundle S)
    (W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.restrictOfNormMeasurability W).majorantDiscrepancy +
      (V.quotientOfNormMeasurability W).majorantDiscrepancy ≤
        V.majorantDiscrepancy := by
  let f := fun ω ↦ Real.log ((V.toNormFamily.restrict W).majorantDiscrepancy ω)
  let g := fun ω ↦ Real.log ((V.toNormFamily.quotient W).majorantDiscrepancy ω)
  have hfg (ω : S.Ω) : f ω + g ω ≤
      Real.log (V.toNormFamily.majorantDiscrepancy ω) := by
    have hp := (V.toNormFamily.restrict W).majorantDiscrepancy_pos ω
    have hq := (V.toNormFamily.quotient W).majorantDiscrepancy_pos ω
    have h := Real.log_le_log (mul_pos hp hq)
      (V.toNormFamily.majorantDiscrepancy_restrict_mul_quotient_le W ω)
    simpa only [Real.log_mul hp.ne' hq.ne'] using h
  change lowerEnvelopeIntegral f S.v + lowerEnvelopeIntegral g S.v ≤
    lowerEnvelopeIntegral (fun ω ↦ Real.log (V.toNormFamily.majorantDiscrepancy ω)) S.v
  exact (lowerEnvelopeIntegral_add_le f g).trans
    (lowerEnvelopeIntegral_mono (Filter.Eventually.of_forall hfg))

/-- Restriction cannot increase the actual global majorant discrepancy. -/
theorem majorantDiscrepancy_restrict_le (V : AdelicVectorBundle S)
    (W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.restrictOfNormMeasurability W).majorantDiscrepancy ≤
      V.majorantDiscrepancy := by
  apply lowerEnvelopeIntegral_mono
  exact Filter.Eventually.of_forall fun ω ↦
    Real.log_le_log ((V.toNormFamily.restrict W).majorantDiscrepancy_pos ω)
      (V.toNormFamily.majorantDiscrepancy_restrict_le W ω)

/-- Quotienting cannot increase the actual global majorant discrepancy. -/
theorem majorantDiscrepancy_quotient_le (V : AdelicVectorBundle S)
    (W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.quotientOfNormMeasurability W).majorantDiscrepancy ≤
      V.majorantDiscrepancy := by
  apply lowerEnvelopeIntegral_mono
  exact Filter.Eventually.of_forall fun ω ↦
    Real.log_le_log ((V.toNormFamily.quotient W).majorantDiscrepancy_pos ω)
      (V.toNormFamily.majorantDiscrepancy_quotient_le W ω)

end ArakelovGeometry.AdelicVectorBundle

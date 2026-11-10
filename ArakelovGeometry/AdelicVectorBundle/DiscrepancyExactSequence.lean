/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.Discrepancy
import ArakelovGeometry.AdelicVectorBundle.MajorantDiscrepancyExactSequence

/-!
# Global majorant discrepancy in an exact sequence

The local elementary-majorant infimum bounds the genuine global lower
integrals of the restricted and quotient bundles. No measurability of the
local infimum or finiteness of the global discrepancy is assumed.
-/

open MeasureTheory

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The two end lower integrals sum to at most the middle lower integral,
also when one or more of these genuine global discrepancies are infinite. -/
theorem majorantDiscrepancy_restrict_add_quotient_le (V : AdelicVectorBundle S E)
    (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.restrictOfMeasurableBase W hS).majorantDiscrepancy hN +
      (V.quotientOfMeasurableBase W hS).majorantDiscrepancy hN ≤
        V.majorantDiscrepancy hN := by
  let f := fun ω ↦ Real.log ((V.toNormFamily.restrict W).majorantDiscrepancy hN ω)
  let g := fun ω ↦ Real.log ((V.toNormFamily.quotient W).majorantDiscrepancy hN ω)
  have hfg (ω : S.Ω) : f ω + g ω ≤
      Real.log (V.toNormFamily.majorantDiscrepancy hN ω) := by
    have hp := (V.toNormFamily.restrict W).majorantDiscrepancy_pos hN ω
    have hq := (V.toNormFamily.quotient W).majorantDiscrepancy_pos hN ω
    have h := Real.log_le_log (mul_pos hp hq)
      (V.toNormFamily.majorantDiscrepancy_restrict_mul_quotient_le hN W ω)
    simpa only [Real.log_mul hp.ne' hq.ne'] using h
  change lowerEnvelopeIntegral f S.v + lowerEnvelopeIntegral g S.v ≤
    lowerEnvelopeIntegral (fun ω ↦ Real.log (V.toNormFamily.majorantDiscrepancy hN ω)) S.v
  exact (lowerEnvelopeIntegral_add_le f g).trans
    (lowerEnvelopeIntegral_mono (Filter.Eventually.of_forall hfg))

/-- Restriction cannot increase the actual global majorant discrepancy. -/
theorem majorantDiscrepancy_restrict_le (V : AdelicVectorBundle S E)
    (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.restrictOfMeasurableBase W hS).majorantDiscrepancy hN ≤
      V.majorantDiscrepancy hN := by
  apply lowerEnvelopeIntegral_mono
  exact Filter.Eventually.of_forall fun ω ↦
    Real.log_le_log ((V.toNormFamily.restrict W).majorantDiscrepancy_pos hN ω)
      (V.toNormFamily.majorantDiscrepancy_restrict_le hN W ω)

/-- Quotienting cannot increase the actual global majorant discrepancy. -/
theorem majorantDiscrepancy_quotient_le (V : AdelicVectorBundle S E)
    (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.quotientOfMeasurableBase W hS).majorantDiscrepancy hN ≤
      V.majorantDiscrepancy hN := by
  apply lowerEnvelopeIntegral_mono
  exact Filter.Eventually.of_forall fun ω ↦
    Real.log_le_log ((V.toNormFamily.quotient W).majorantDiscrepancy_pos hN ω)
      (V.toNormFamily.majorantDiscrepancy_quotient_le hN W ω)

end ArakelovGeometry.AdelicVectorBundle

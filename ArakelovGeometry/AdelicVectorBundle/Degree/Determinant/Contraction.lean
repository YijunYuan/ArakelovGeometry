/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Map
import ArakelovGeometry.AdelicVectorBundle.Operator.LineHeight
import ArakelovGeometry.MeasureTheory.Integral.UpperEnvelope
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Degree comparison for actual measurable determinants

A genuine completed contraction compares the degrees of the actual determinant
lines. The hypotheses concern their actual norm measurability; no discrete or
common-density condition on the place space is needed.
-/

@[expose] public section

open MeasureTheory Filter
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v w w'
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Every completed contraction compares the degrees of the actual measurable
determinants, without regularity of the place space, including rank zero. -/
theorem degreeOfMeasurableDeterminant_le_of_completed_contraction [S.IsProper]
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    [hdetV : V.toNormFamily.determinant.IsMeasurable]
    [hdetW : W.toNormFamily.determinant.IsMeasurable]
    [hN : S.IsArchimedeanNormalized]
    (he : ∀ ω z, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion z) ≤ V.toNormFamily.norm ω z) :
    V.degreeOfMeasurableDeterminant ≤ W.degreeOfMeasurableDeterminant := by
  let DV := V.determinant
  let DW := W.determinant
  let d := determinantMap K e.toLinearMap e.finrank_eq
  have hd : d ≠ 0 :=
    determinantMap_ne_zero_of_injective e.toLinearMap e.finrank_eq e.injective
  have hl := lowerEnvelopeIntegral_mono (μ := S.v) (Eventually.of_forall
    (fun ω ↦ Real.log_nonpos
      (V.toNormFamily.determinant.operatorNorm_nonneg W.toNormFamily.determinant ω d)
      ((V.toNormFamily.determinantMap_operatorNorm_le_pow W.toNormFamily ω
        e.toLinearMap e.finrank_eq).trans
        (pow_le_one₀ (V.toNormFamily.operatorNorm_nonneg W.toNormFamily ω e.toLinearMap)
          (V.toNormFamily.operatorNorm_le W.toNormFamily ω e.toLinearMap (by norm_num)
            (by intro z; simpa only [one_mul] using he ω z))))))
  change lowerEnvelopeIntegral (DV.toNormFamily.localHeight DW.toNormFamily ⟨d, hd⟩) S.v ≤ _
    at hl
  have hm : DV.mapHeight DW d =
      ((V.degreeOfMeasurableDeterminant -
        W.degreeOfMeasurableDeterminant : ℝ) : EReal) :=
    DV.mapHeight_eq_lineDegree_sub DW (hV := (V.determinant_isLine))
      (hW := (W.determinant_isLine)) hd
  rw [← DV.mapHeight_eq_lowerEnvelopeIntegral DW hd, hm,
    lowerEnvelopeIntegral_eq_integral
      (show Integrable (fun _ : S.Ω ↦ (0 : ℝ)) S.v from integrable_zero S.Ω ℝ S.v),
    integral_zero] at hl
  exact sub_nonpos.mp (EReal.coe_le_coe_iff.mp hl)

end ArakelovGeometry.AdelicVectorBundle

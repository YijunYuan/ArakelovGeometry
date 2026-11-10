/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Majorant.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Majorant.Bound
import ArakelovGeometry.MeasureTheory.Integral.UpperEnvelope
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Global discrepancy numbers

Definition4.3.12 uses the actual integral of logarithmic determinant
discrepancy and the lower-envelope integral of logarithmic majorant
discrepancy. The latter does not assume measurability of the infimum.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The integral of the actual local determinant discrepancy. -/
def determinantDiscrepancy (V : AdelicVectorBundle S E) : ℝ :=
  ∫ ω, Real.log (V.toNormFamily.determinantDiscrepancy ω) ∂S.v

/-- The actual lower integral of the local elementary-majorant infimum. -/
def majorantDiscrepancy (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : EReal :=
  lowerEnvelopeIntegral (fun ω ↦ Real.log (V.toNormFamily.majorantDiscrepancy hN ω)) S.v

/-- The global determinant discrepancy is nonnegative. -/
theorem determinantDiscrepancy_nonneg (V : AdelicVectorBundle S E) :
    0 ≤ V.determinantDiscrepancy :=
  integral_nonneg V.toNormFamily.log_determinantDiscrepancy_nonneg

/-- A zero lower envelope puts the global majorant discrepancy in [0,+∞]. -/
theorem majorantDiscrepancy_nonneg (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    0 ≤ V.majorantDiscrepancy hN :=
  lowerEnvelopeIntegral_nonneg
    (Filter.Eventually.of_forall (V.toNormFamily.log_majorantDiscrepancy_nonneg hN))

/-- Strong domination makes the actual lower integral finite from above. -/
theorem IsStronglyAdelic.majorantDiscrepancy_lt_top
    {V : AdelicVectorBundle S E} (hV : V.IsStronglyAdelic)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.majorantDiscrepancy hN < ⊤ := by
  obtain ⟨A, hA, hfA⟩ := (hV.log_majorantDiscrepancy_hasIntegrableBounds hN).1
  have h := lowerEnvelopeIntegral_mono hfA
  rw [lowerEnvelopeIntegral_eq_integral hA] at h
  exact h.trans_lt (EReal.coe_lt_top _)

/-- Nonnegativity excludes the other infinite value in every rank. -/
theorem bot_lt_majorantDiscrepancy (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ⊥ < V.majorantDiscrepancy hN :=
  (EReal.bot_lt_coe 0).trans_le (V.majorantDiscrepancy_nonneg hN)

/-- The actual determinant-discrepancy integral is the degree-duality defect. -/
theorem determinantDiscrepancy_eq_degree_add_degree_dual [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.determinantDiscrepancy =
      V.degree hS hN + (V.dualOfMeasurableBase hS).degree hS hN :=
  (V.degree_add_degree_dual_eq_integral_log_determinantDiscrepancy hS hN).symm

/-- Pointwise δ≤Δ passes to the real integral and the actual lower integral.
The local determinant function is integrable under the standing alternative. -/
theorem determinantDiscrepancy_le_majorantDiscrepancy (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.determinantDiscrepancy : EReal) ≤ V.majorantDiscrepancy hN := by
  have h := lowerEnvelopeIntegral_mono (μ := S.v)
    (Filter.Eventually.of_forall fun ω ↦
      Real.log_le_log (V.toNormFamily.determinantDiscrepancy_pos ω)
        (V.toNormFamily.determinantDiscrepancy_le_majorantDiscrepancy hN ω))
  rw [lowerEnvelopeIntegral_eq_integral (V.integrable_log_determinantDiscrepancy hS hN)]
    at h
  exact h

/-- A Hermitian family has zero global determinant discrepancy. -/
theorem determinantDiscrepancy_eq_zero_of_isHermitian (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) : V.determinantDiscrepancy = 0 := by
  simp only [determinantDiscrepancy,
    hV.determinantDiscrepancy_eq_one V.toNormFamily, Real.log_one, integral_zero]

/-- A Hermitian family has zero actual lower majorant-discrepancy integral. -/
theorem majorantDiscrepancy_eq_zero_of_isHermitian (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) : V.majorantDiscrepancy hN = 0 := by
  have he : (fun ω ↦ Real.log (V.toNormFamily.majorantDiscrepancy hN ω)) = 0 := by
    funext ω
    rw [hV.majorantDiscrepancy_eq_one, Real.log_one]
    rfl
  rw [majorantDiscrepancy, he,
    lowerEnvelopeIntegral_eq_integral (integrable_zero S.Ω ℝ S.v)]
  simp only [Pi.zero_apply, integral_zero, EReal.coe_zero]

/-- The unit determinant of the zero vector space has zero global discrepancy. -/
theorem determinantDiscrepancy_eq_zero_of_finrank_eq_zero (V : AdelicVectorBundle S E)
    (hr : Module.finrank K E = 0) : V.determinantDiscrepancy = 0 := by
  simp only [determinantDiscrepancy,
    V.toNormFamily.determinantDiscrepancy_eq_one_of_finrank_eq_zero hr,
    Real.log_one, integral_zero]

/-- The explicit rank-zero infimum convention gives zero global lower integral. -/
theorem majorantDiscrepancy_eq_zero_of_finrank_eq_zero (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) : V.majorantDiscrepancy hN = 0 := by
  have he : (fun ω ↦ Real.log (V.toNormFamily.majorantDiscrepancy hN ω)) = 0 := by
    funext ω
    rw [V.toNormFamily.majorantDiscrepancy_eq_one_of_finrank_eq_zero hN hr, Real.log_one]
    rfl
  rw [majorantDiscrepancy, he,
    lowerEnvelopeIntegral_eq_integral (integrable_zero S.Ω ℝ S.v)]
  simp only [Pi.zero_apply, integral_zero, EReal.coe_zero]

end

end ArakelovGeometry.AdelicVectorBundle

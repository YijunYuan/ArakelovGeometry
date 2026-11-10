/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Destabilizing
import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Dual
import ArakelovGeometry.AdelicVectorBundle.Slope.DualUpper
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Hermitian semistability, quotients, and duality

The genuine Hermitian restriction--quotient degree equality identifies the
subspace and quotient semistability criteria. The actual quotient-mean
infimum then gives the minimal-slope criterion. All source equivalences
retain positive rank; the degree-deficit identity includes zero ranks.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Exact Hermitian additivity expresses every quotient degree deficit as
the opposite restriction degree deficit, including zero ends. -/
theorem degree_quotient_sub_rank_mul_slope_eq_rank_mul_slope_sub_degree_restrict_of_isHermitian
    (V : AdelicVectorBundle S E) (U : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    (V.quotientOfMeasurableBase U hS).degree hS hN -
        (Module.finrank K (E ⧸ U) : ℝ) * V.slope hS hN =
      (Module.finrank K U : ℝ) * V.slope hS hN -
        (V.restrictOfMeasurableBase U hS).degree hS hN := by
  have hd := V.degree_restrict_add_degree_quotient_eq_of_isHermitian U hS hN hV
  rw [V.degree_eq_rank_mul_slope hS hN] at hd
  have hr : (Module.finrank K (E ⧸ U) : ℝ) + Module.finrank K U =
      Module.finrank K E := by exact_mod_cast U.finrank_quotient_add_finrank
  rw [← hr, add_mul] at hd
  linarith

/-- For a positive-rank actual Hermitian bundle, subspace semistability is
equivalent to the mean-slope lower bound for every nonzero actual quotient. -/
theorem isMeanSlopeSemistable_iff_slope_le_quotient_of_isHermitian
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hr : 0 < Module.finrank K E) :
    V.IsMeanSlopeSemistable hS hN ↔
      ∀ U : Submodule K E, 0 < Module.finrank K (E ⧸ U) →
        V.slope hS hN ≤ (V.quotientOfMeasurableBase U hS).slope hS hN := by
  constructor
  · intro hs U hQ
    have hR : (V.restrictOfMeasurableBase U hS).degree hS hN ≤
        (Module.finrank K U : ℝ) * V.slope hS hN := by
      by_cases hU : 0 < Module.finrank K U
      · rw [(V.restrictOfMeasurableBase U hS).degree_eq_rank_mul_slope hS hN]
        exact mul_le_mul_of_nonneg_left (hs.2 U hU) (Nat.cast_nonneg _)
      · have hz : Module.finrank K U = 0 := Nat.eq_zero_of_not_pos hU
        rw [hz, Nat.cast_zero, zero_mul,
          (V.restrictOfMeasurableBase U hS).degree_eq_zero_of_finrank_eq_zero hS hN hz]
    have hd :=
      V.degree_quotient_sub_rank_mul_slope_eq_rank_mul_slope_sub_degree_restrict_of_isHermitian
        U hS hN hV
    rw [(V.quotientOfMeasurableBase U hS).degree_eq_rank_mul_slope hS hN] at hd
    have hp : (0 : ℝ) < Module.finrank K (E ⧸ U) := Nat.cast_pos.mpr hQ
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith
  · intro hQ
    refine ⟨hr, fun U hU => ?_⟩
    by_contra hR
    obtain ⟨hpos, _, hlt⟩ := V.quotient_rank_and_slope_lt_of_lt_restrict U hU
      hS hN (V.slope hS hN) le_rfl (lt_of_not_ge hR)
    exact (not_lt_of_ge (hQ U hpos)) hlt

/-- The actual quotient-mean infimum identifies Hermitian semistability
with equality of the extended-real minimum and real mean. -/
theorem isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hr : 0 < Module.finrank K E) :
    V.IsMeanSlopeSemistable hS hN ↔ V.minimalSlope hS hN = (V.slope hS hN : EReal) := by
  rw [V.isMeanSlopeSemistable_iff_slope_le_quotient_of_isHermitian hS hN hV hr]
  constructor
  · intro hQ
    apply le_antisymm (V.minimalSlope_le_slope hS hN hr)
    rw [V.minimalSlope_eq_iInf_slope_quotient hS hN]
    exact le_iInf fun U => EReal.coe_le_coe_iff.mpr (hQ U.val U.property)
  · intro he U hU
    exact EReal.coe_le_coe_iff.mp
      (he ▸ V.minimalSlope_le_slope_quotient U hU hS hN)

/-- The actual Hermitian dual is mean-slope semistable exactly when the
original positive-rank bundle is. The finite real representatives used in
the proof come from the accepted extremal-slope finiteness theorem. -/
theorem isMeanSlopeSemistable_dual_iff_of_isHermitian
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hr : 0 < Module.finrank K E) :
    (V.dualOfMeasurableBase hS).IsMeanSlopeSemistable hS hN ↔
      V.IsMeanSlopeSemistable hS hN := by
  have hrD : 0 < Module.finrank K (Module.Dual K E) := by
    rwa [Subspace.dual_finrank_eq]
  have hVD : (V.dualOfMeasurableBase hS).toNormFamily.IsHermitian hN := hV.dual
  rw [(V.dualOfMeasurableBase hS).isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian
      hS hN hVD hrD,
    V.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hS hN hr]
  obtain ⟨a, ha⟩ := (V.dualOfMeasurableBase hS).exists_minimalSlope_eq_coe hS hN hrD
  obtain ⟨b, hb⟩ := V.exists_maximalSlope_eq_coe hS hN hr
  have hext := V.minimalSlope_dual_add_maximalSlope_eq_zero_of_isHermitian hS hN hV hr
  rw [ha, hb, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_eq_coe_iff] at hext
  have hmean := V.slope_add_slope_dual_eq_zero_of_isHermitian hS hN hV
  rw [ha, hb, EReal.coe_eq_coe_iff, EReal.coe_eq_coe_iff]
  constructor <;> intro he <;> linarith

end

end ArakelovGeometry.AdelicVectorBundle

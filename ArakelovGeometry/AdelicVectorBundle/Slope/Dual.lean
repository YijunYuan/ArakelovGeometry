/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic
import ArakelovGeometry.AdelicVectorBundle.Dual.Restriction
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The source conditional first dual slope inequality

Actual completed quotient-dual annihilator isometries and the nonnegative
degree-duality defect bound each quotient slope from below. Source4.3.25's
finite-dual-maximal-slope hypothesis remains explicit; source4.3.30 is a
separate finiteness producer.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The nonnegative actual degree-duality defect gives nonnegative sum of
mean slopes, including the explicit zero-rank mean-slope conventions. -/
theorem slope_add_slope_dual_nonneg (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    0 ≤ V.slope + (V.dualOfMeasurableBase).slope := by
  have hd : 0 ≤ V.degree + (V.dualOfMeasurableBase).degree := by
    rw [← V.determinantDiscrepancy_eq_degree_add_degree_dual]
    exact V.determinantDiscrepancy_nonneg
  rw [slope, slope, Subspace.dual_finrank_eq, ← add_div]
  exact div_nonneg hd (Nat.cast_nonneg _)

/-- The actual quotient-dual annihilator isometry identifies mean slopes,
not merely comparable degrees, on the canonical source subspace. -/
theorem slope_dual_quotient_eq_slope_restrict_annihilator (V : AdelicVectorBundle S)
    (W : Submodule K V)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    ((V.quotientOfMeasurableBase W).dualOfMeasurableBase).slope =
      ((V.dualOfMeasurableBase).restrictOfMeasurableBase W.dualAnnihilator).slope
        := by
  apply slope_eq_of_completed_isometry _ _ W.dualQuotEquivDualAnnihilator
  intro ω z
  exact (V.toNormFamily.quotient_dual_annihilator_norm_eq W ω z).symm

/-- Every nonzero quotient dual has mean slope bounded by the actual ambient
dual maximal slope, through the completed annihilator isometry. -/
theorem slope_dual_quotient_le_maximalSlope_dual (V : AdelicVectorBundle S)
    (W : Submodule K V) (hW : 0 < Module.finrank K (V ⧸ W))
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (((V.quotientOfMeasurableBase W).dualOfMeasurableBase).slope : EReal) ≤
      (V.dualOfMeasurableBase).maximalSlope := by
  rw [V.slope_dual_quotient_eq_slope_restrict_annihilator W]
  apply (V.dualOfMeasurableBase).slope_restrict_le_maximalSlope W.dualAnnihilator _
  rw [← W.dualQuotEquivDualAnnihilator.finrank_eq, Subspace.dual_finrank_eq]
  exact hW

/-- Each nonzero actual quotient satisfies the local input to source(4.46).
The source minimal slope remains the infimum of these quotient maximal slopes. -/
theorem maximalSlope_quotient_add_maximalSlope_dual_nonneg
    (V : AdelicVectorBundle S) (W : Submodule K V)
    (hW : 0 < Module.finrank K (V ⧸ W))
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    0 ≤ (V.quotientOfMeasurableBase W).maximalSlope +
      (V.dualOfMeasurableBase).maximalSlope := by
  have h0 := (V.quotientOfMeasurableBase W).slope_add_slope_dual_nonneg
  have hs := (V.quotientOfMeasurableBase W).slope_le_maximalSlope hW
  have hd := V.slope_dual_quotient_le_maximalSlope_dual W hW
  have h0' : 0 ≤ ((V.quotientOfMeasurableBase W).slope : EReal) +
      (((V.quotientOfMeasurableBase W).dualOfMeasurableBase).slope : EReal) := by
    rw [← EReal.coe_add, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    exact h0
  exact h0'.trans (add_le_add hs hd)

/-- The finite dual maximal slope in source4.3.25 gives a finite lower bound
for the actual source minimal slope. The finiteness premise is retained. -/
theorem neg_maximalSlope_dual_le_minimalSlope_of_lt_top (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V)
    (hfin : (V.dualOfMeasurableBase).maximalSlope < ⊤) :
    -(V.dualOfMeasurableBase).maximalSlope ≤ V.minimalSlope := by
  have hq := V.maximalSlope_quotient_add_maximalSlope_dual_nonneg
  have hrD : 0 < Module.finrank K (Module.Dual K V) := by
    rwa [Subspace.dual_finrank_eq]
  have hb := (V.dualOfMeasurableBase).bot_lt_maximalSlope hrD
  lift (V.dualOfMeasurableBase).maximalSlope to ℝ using
    ⟨hfin.ne, hb.ne'⟩ with c
  apply V.le_minimalSlope
  intro W hW
  have h := hq W hW
  simpa only [zero_sub] using EReal.sub_le_of_le_add h

/-- Source Proposition4.3.25 and equation(4.46), with the source's explicitly
stated finite-dual-maximal-slope hypothesis still visible. -/
theorem minimalSlope_add_maximalSlope_dual_nonneg_of_lt_top
    (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V)
    (hfin : (V.dualOfMeasurableBase).maximalSlope < ⊤) :
    0 ≤ V.minimalSlope + (V.dualOfMeasurableBase).maximalSlope := by
  have h := V.neg_maximalSlope_dual_le_minimalSlope_of_lt_top hr hfin
  have hrD : 0 < Module.finrank K (Module.Dual K V) := by
    rwa [Subspace.dual_finrank_eq]
  have hb := (V.dualOfMeasurableBase).bot_lt_maximalSlope hrD
  lift (V.dualOfMeasurableBase).maximalSlope to ℝ using
    ⟨hfin.ne, hb.ne'⟩ with c
  have hi := add_le_add_right h (c : EReal)
  simpa only [← EReal.coe_neg, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_comm] using hi

/-- Under source4.3.25's finite-dual-max premise, the minimal slope cannot
be minus infinity. Its upper finiteness remains a separate producer. -/
theorem bot_lt_minimalSlope_of_maximalSlope_dual_lt_top (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (hr : 0 < Module.finrank K V)
    (hfin : (V.dualOfMeasurableBase).maximalSlope < ⊤) :
    ⊥ < V.minimalSlope := by
  have h := V.neg_maximalSlope_dual_le_minimalSlope_of_lt_top hr hfin
  have hrD : 0 < Module.finrank K (Module.Dual K V) := by
    rwa [Subspace.dual_finrank_eq]
  have hb := (V.dualOfMeasurableBase).bot_lt_maximalSlope hrD
  lift (V.dualOfMeasurableBase).maximalSlope to ℝ using
    ⟨hfin.ne, hb.ne'⟩ with c
  rw [← EReal.coe_neg] at h
  exact (EReal.bot_lt_coe _).trans_le h

end

end ArakelovGeometry.AdelicVectorBundle

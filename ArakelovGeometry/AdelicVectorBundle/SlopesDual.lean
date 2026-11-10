/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Discrepancy
public import ArakelovGeometry.AdelicVectorBundle.DualRestriction
public import ArakelovGeometry.AdelicVectorBundle.Slopes

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

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The nonnegative actual degree-duality defect gives nonnegative sum of
mean slopes, including the explicit zero-rank mean-slope conventions. -/
theorem slope_add_slope_dual_nonneg (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    0 ≤ V.slope hS hN + (V.dualOfMeasurableBase hS).slope hS hN := by
  have hd : 0 ≤ V.degree hS hN + (V.dualOfMeasurableBase hS).degree hS hN := by
    rw [← V.determinantDiscrepancy_eq_degree_add_degree_dual hS hN]
    exact V.determinantDiscrepancy_nonneg
  rw [slope, slope, Subspace.dual_finrank_eq, ← add_div]
  exact div_nonneg hd (Nat.cast_nonneg _)

/-- The actual quotient-dual annihilator isometry identifies mean slopes,
not merely comparable degrees, on the canonical source subspace. -/
theorem slope_dual_quotient_eq_slope_restrict_annihilator (V : AdelicVectorBundle S E)
    (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.quotientOfMeasurableBase W hS).dualOfMeasurableBase hS).slope hS hN =
      ((V.dualOfMeasurableBase hS).restrictOfMeasurableBase W.dualAnnihilator hS).slope
        hS hN := by
  apply slope_eq_of_completed_isometry _ _ W.dualQuotEquivDualAnnihilator hS hN
  intro ω z
  simp only [dualOfMeasurableBase_toNormFamily, quotientOfMeasurableBase_toNormFamily,
    restrictOfMeasurableBase_toNormFamily]
  exact (V.toNormFamily.quotient_dual_annihilator_norm_eq W ω z).symm

/-- Every nonzero quotient dual has mean slope bounded by the actual ambient
dual maximal slope, through the completed annihilator isometry. -/
theorem slope_dual_quotient_le_maximalSlope_dual (V : AdelicVectorBundle S E)
    (W : Submodule K E) (hW : 0 < Module.finrank K (E ⧸ W))
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (((V.quotientOfMeasurableBase W hS).dualOfMeasurableBase hS).slope hS hN : EReal) ≤
      (V.dualOfMeasurableBase hS).maximalSlope hS hN := by
  rw [V.slope_dual_quotient_eq_slope_restrict_annihilator W hS hN]
  apply (V.dualOfMeasurableBase hS).slope_restrict_le_maximalSlope W.dualAnnihilator _ hS hN
  rw [← W.dualQuotEquivDualAnnihilator.finrank_eq, Subspace.dual_finrank_eq]
  exact hW

/-- Each nonzero actual quotient satisfies the local input to source(4.46).
The source minimal slope remains the infimum of these quotient maximal slopes. -/
theorem maximalSlope_quotient_add_maximalSlope_dual_nonneg
    (V : AdelicVectorBundle S E) (W : Submodule K E)
    (hW : 0 < Module.finrank K (E ⧸ W))
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    0 ≤ (V.quotientOfMeasurableBase W hS).maximalSlope hS hN +
      (V.dualOfMeasurableBase hS).maximalSlope hS hN := by
  have h0 := (V.quotientOfMeasurableBase W hS).slope_add_slope_dual_nonneg hS hN
  have hs := (V.quotientOfMeasurableBase W hS).slope_le_maximalSlope hS hN hW
  have hd := V.slope_dual_quotient_le_maximalSlope_dual W hW hS hN
  have h0' : 0 ≤ ((V.quotientOfMeasurableBase W hS).slope hS hN : EReal) +
      (((V.quotientOfMeasurableBase W hS).dualOfMeasurableBase hS).slope hS hN : EReal) := by
    rw [← EReal.coe_add, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    exact h0
  exact h0'.trans (add_le_add hs hd)

/-- The finite dual maximal slope in source4.3.25 gives a finite lower bound
for the actual source minimal slope. The finiteness premise is retained. -/
theorem neg_maximalSlope_dual_le_minimalSlope_of_lt_top (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E)
    (hfin : (V.dualOfMeasurableBase hS).maximalSlope hS hN < ⊤) :
    -(V.dualOfMeasurableBase hS).maximalSlope hS hN ≤ V.minimalSlope hS hN := by
  have hq := V.maximalSlope_quotient_add_maximalSlope_dual_nonneg
  have hrD : 0 < Module.finrank K (Module.Dual K E) := by
    rwa [Subspace.dual_finrank_eq]
  have hb := (V.dualOfMeasurableBase hS).bot_lt_maximalSlope hS hN hrD
  lift (V.dualOfMeasurableBase hS).maximalSlope hS hN to ℝ using
    ⟨hfin.ne, hb.ne'⟩ with c
  apply V.le_minimalSlope hS hN
  intro W hW
  have h := hq W hW hS hN
  simpa only [zero_sub] using EReal.sub_le_of_le_add h

/-- Source Proposition4.3.25 and equation(4.46), with the source's explicitly
stated finite-dual-maximal-slope hypothesis still visible. -/
theorem minimalSlope_add_maximalSlope_dual_nonneg_of_lt_top
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E)
    (hfin : (V.dualOfMeasurableBase hS).maximalSlope hS hN < ⊤) :
    0 ≤ V.minimalSlope hS hN + (V.dualOfMeasurableBase hS).maximalSlope hS hN := by
  have h := V.neg_maximalSlope_dual_le_minimalSlope_of_lt_top hS hN hr hfin
  have hrD : 0 < Module.finrank K (Module.Dual K E) := by
    rwa [Subspace.dual_finrank_eq]
  have hb := (V.dualOfMeasurableBase hS).bot_lt_maximalSlope hS hN hrD
  lift (V.dualOfMeasurableBase hS).maximalSlope hS hN to ℝ using
    ⟨hfin.ne, hb.ne'⟩ with c
  have hi := add_le_add_right h (c : EReal)
  simpa only [← EReal.coe_neg, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_comm] using hi

/-- Under source4.3.25's finite-dual-max premise, the minimal slope cannot
be minus infinity. Its upper finiteness remains a separate producer. -/
theorem bot_lt_minimalSlope_of_maximalSlope_dual_lt_top (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E)
    (hfin : (V.dualOfMeasurableBase hS).maximalSlope hS hN < ⊤) :
    ⊥ < V.minimalSlope hS hN := by
  have h := V.neg_maximalSlope_dual_le_minimalSlope_of_lt_top hS hN hr hfin
  have hrD : 0 < Module.finrank K (Module.Dual K E) := by
    rwa [Subspace.dual_finrank_eq]
  have hb := (V.dualOfMeasurableBase hS).bot_lt_maximalSlope hS hN hrD
  lift (V.dualOfMeasurableBase hS).maximalSlope hS hN to ℝ using
    ⟨hfin.ne, hb.ne'⟩ with c
  rw [← EReal.coe_neg] at h
  exact (EReal.bot_lt_coe _).trans_le h

end

end ArakelovGeometry.AdelicVectorBundle

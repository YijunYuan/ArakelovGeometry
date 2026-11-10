/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeneralHNModified
import ArakelovGeometry.AdelicVectorBundle.GeneralHNUpper
import ArakelovGeometry.AdelicVectorBundle.DegreeFlagMajorant
import ArakelovGeometry.AdelicVectorBundle.DegreeFlagDual

/-!
# Modified degrees in actual exhaustive flags

Each factor carries its actual restriction and quotient norms. The genuine
flag degree inequalities combine with the general ordered degree bounds.
Capital discrepancy may be infinite; repeated terms and zero rank are allowed.
The final term is required to be the entire space.
-/

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w

private theorem modifiedFlag_coe_sum {n : ℕ} (f : Fin n → ℝ) :
    ((∑ i, f i : ℝ) : EReal) = ∑ i, (f i : EReal) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, EReal.coe_add, ih]

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  {n : ℕ} (F : Fin (n + 1) → Submodule K E)

/-- Genuine modified factor degrees are bounded by the ambient ordinary degree. -/
theorem sum_flagQuotient_modifiedDegree_le
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤) :
    (∑ i : Fin n, (V.flagQuotientOfMeasurableBase F hS i).modifiedDegree hS hN) ≤
    V.degree hS hN := by
  apply le_trans _ (V.sum_flagQuotient_degree_le F hF hzero htop hS hN)
  exact Finset.sum_le_sum (fun i _ ↦ modifiedDegree_le_degree
    (V.flagQuotientOfMeasurableBase F hS i) hS hN)

/-- Actual capital discrepancy bounds the sum of genuine modified factor degrees. -/
theorem degree_sub_majorantDiscrepancy_le_sum_flagQuotient_modifiedDegree
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤) :
    (V.degree hS hN : EReal) - V.majorantDiscrepancy hN ≤
    ((∑ i : Fin n, (V.flagQuotientOfMeasurableBase F hS i).modifiedDegree hS hN : ℝ) : EReal) := by
  rw [modifiedFlag_coe_sum]
  apply (V.degree_sub_majorantDiscrepancy_le_sum_flagQuotient F hF hzero htop hS hN).trans
  apply Finset.sum_le_sum
  intro i _
  exact degree_sub_majorantDiscrepancy_le_sum_generalHNOrderedSlope
    (V.flagQuotientOfMeasurableBase F hS i) hS hN

/-- The actual determinant-discrepancy version under finite-place ultrametricity. -/
theorem degree_sub_determinantDiscrepancy_le_sum_flagQuotient_modifiedDegree
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (hV : V.IsUltrametric) : V.degree hS hN - V.determinantDiscrepancy ≤
    ∑ i : Fin n, (V.flagQuotientOfMeasurableBase F hS i).modifiedDegree hS hN := by
  apply (V.degree_sub_determinantDiscrepancy_le_sum_flagQuotient
    F hF hzero htop hS hN hV).trans
  apply Finset.sum_le_sum
  intro i _
  have hQ : (V.flagQuotientOfMeasurableBase F hS i).IsUltrametric := by
    simpa only [flagQuotientOfMeasurableBase, quotientOfMeasurableBase_toNormFamily,
      restrictOfMeasurableBase_toNormFamily] using
      (hV.restrict (F i.succ)).quotient ((F i.castSucc).comap (F i.succ).subtype)
  exact degree_sub_determinantDiscrepancy_le_sum_generalHNOrderedSlope
    (V.flagQuotientOfMeasurableBase F hS i) hS hN hQ

end

end ArakelovGeometry.AdelicVectorBundle

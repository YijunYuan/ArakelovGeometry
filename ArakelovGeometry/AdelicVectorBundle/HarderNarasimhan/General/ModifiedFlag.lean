/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic
public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Modified

import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Dual
import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Majorant
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Upper
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Modified degrees in actual exhaustive flags

Each factor carries its actual restriction and quotient norms. The genuine
flag degree inequalities combine with the general ordered degree bounds.
Capital discrepancy may be infinite; repeated terms and zero rank are allowed.
The final term is required to be the entire space.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

private theorem modifiedFlag_coe_sum {n : ℕ} (f : Fin n → ℝ) :
    ((∑ i, f i : ℝ) : EReal) = ∑ i, (f i : EReal) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, EReal.coe_add, ih]

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]
  {n : ℕ} (F : Fin (n + 1) → Submodule K V)

/-- Genuine modified factor degrees are bounded by the ambient ordinary degree. -/
theorem sum_flagQuotient_modifiedDegree_le
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤) :
    (∑ i : Fin n, (V.flagQuotientOfMeasurableBase F i).modifiedDegree) ≤
    V.degree := by
  apply le_trans _ (V.sum_flagQuotient_degree_le F hF hzero htop)
  exact Finset.sum_le_sum (fun i _ ↦ modifiedDegree_le_degree
    (V.flagQuotientOfMeasurableBase F i))

/-- Actual capital discrepancy bounds the sum of genuine modified factor degrees. -/
theorem degree_sub_majorantDiscrepancy_le_sum_flagQuotient_modifiedDegree
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤) :
    (V.degree : EReal) - V.majorantDiscrepancy ≤
    ((∑ i : Fin n, (V.flagQuotientOfMeasurableBase F i).modifiedDegree : ℝ) : EReal) := by
  rw [modifiedFlag_coe_sum]
  apply (V.degree_sub_majorantDiscrepancy_le_sum_flagQuotient F hF hzero htop).trans
  apply Finset.sum_le_sum
  intro i _
  exact degree_sub_majorantDiscrepancy_le_sum_generalHNOrderedSlope
    (V.flagQuotientOfMeasurableBase F i)

/-- The actual determinant-discrepancy version under finite-place ultrametricity. -/
theorem degree_sub_determinantDiscrepancy_le_sum_flagQuotient_modifiedDegree
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    [hV : V.toNormFamily.IsUltrametric] : V.degree - V.determinantDiscrepancy ≤
    ∑ i : Fin n, (V.flagQuotientOfMeasurableBase F i).modifiedDegree := by
  apply (V.degree_sub_determinantDiscrepancy_le_sum_flagQuotient
    F hF hzero htop).trans
  apply Finset.sum_le_sum
  intro i _
  have hQ : (V.flagQuotientOfMeasurableBase F i).toNormFamily.IsUltrametric := by
    simpa only [flagQuotientOfMeasurableBase, quotientOfMeasurableBase_toNormFamily,
      restrictOfMeasurableBase_toNormFamily] using
      (hV.restrict (F i.succ)).quotient ((F i.castSucc).comap (F i.succ).subtype)
  exact degree_sub_determinantDiscrepancy_le_sum_generalHNOrderedSlope
    (V.flagQuotientOfMeasurableBase F i) (hV := hQ)

end

end ArakelovGeometry.AdelicVectorBundle

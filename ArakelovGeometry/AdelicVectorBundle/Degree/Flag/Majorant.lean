/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic
public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Majorant.Isometry
import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Majorant
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The capital-discrepancy degree bound for actual finite flags

The genuine two-step majorant bound applies in each restricted bundle.
Canonical nested restrictions preserve degree and the actual majorant
infimum. Extended-real inequalities include infinite global discrepancies,
empty segments, and repeated terms of the flag.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Degree minus the actual global capital discrepancy is bounded by the
sum over the actual successive quotients of every finite flag starting at zero.
The terms are extended real, so infinite discrepancies are retained. -/
theorem degree_restrict_sub_majorantDiscrepancy_le_sum_flagQuotient [S.IsProper]
    (V : AdelicVectorBundle S) {n : ℕ} (F : Fin (n + 1) → Submodule K V)
    (hF : Monotone F) (hzero : F 0 = ⊥)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    ((V.restrictOfMeasurableBase (F (Fin.last n))).degree : EReal) -
        (V.restrictOfMeasurableBase (F (Fin.last n))).majorantDiscrepancy ≤
      ∑ i : Fin n, (((V.flagQuotientOfMeasurableBase F i).degree : EReal) -
        (V.flagQuotientOfMeasurableBase F i).majorantDiscrepancy) := by
  induction n with
  | zero =>
      have hz : F (Fin.last 0) = ⊥ := hzero
      have hr : Module.finrank K (F (Fin.last 0)) = 0 := by
        rw [hz]
        exact finrank_bot K V
      have hd := degree_eq_zero_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (F (Fin.last 0))) hr
      have hΔ := majorantDiscrepancy_eq_zero_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (F (Fin.last 0))) hr
      simp only [Fin.sum_univ_zero, hd, hΔ, EReal.coe_zero, sub_zero, le_refl]
  | succ n ih =>
      let G : Fin (n + 1) → Submodule K V := fun i ↦ F i.castSucc
      let U : Submodule K V := F (Fin.last n).castSucc
      let W : Submodule K V := F (Fin.last (n + 1))
      have hG : Monotone G := hF.comp Fin.strictMono_castSucc.monotone
      have hzG : G 0 = ⊥ := hzero
      have hprefix := ih G hG hzG
      change ((V.restrictOfMeasurableBase U).degree : EReal) -
          (V.restrictOfMeasurableBase U).majorantDiscrepancy ≤
        ∑ i : Fin n,
          (((V.flagQuotientOfMeasurableBase F i.castSucc).degree : EReal) -
          (V.flagQuotientOfMeasurableBase F i.castSucc).majorantDiscrepancy) at hprefix
      have hUW : U ≤ W := hF (Fin.le_last _)
      have hstep := degree_sub_majorantDiscrepancy_le_restrict_add_quotient
        (V.restrictOfMeasurableBase W) (U.comap W.subtype)
      rw [V.degree_restrict_restrict U W hUW,
        V.majorantDiscrepancy_restrict_restrict U W hUW] at hstep
      change ((V.restrictOfMeasurableBase W).degree : EReal) -
          (V.restrictOfMeasurableBase W).majorantDiscrepancy ≤
        (((V.restrictOfMeasurableBase U).degree : EReal) -
          (V.restrictOfMeasurableBase U).majorantDiscrepancy) +
        (((V.flagQuotientOfMeasurableBase F (Fin.last n)).degree : EReal) -
          (V.flagQuotientOfMeasurableBase F (Fin.last n)).majorantDiscrepancy) at hstep
      rw [Fin.sum_univ_castSucc]
      exact hstep.trans (add_le_add_left hprefix _)

/-- Source equation (4.27) for every complete actual finite flag. No original
ultrametricity or finiteness of the global majorant discrepancies is assumed. -/
theorem degree_sub_majorantDiscrepancy_le_sum_flagQuotient [S.IsProper]
    (V : AdelicVectorBundle S) {n : ℕ} (F : Fin (n + 1) → Submodule K V)
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (V.degree : EReal) - V.majorantDiscrepancy ≤
      ∑ i : Fin n, (((V.flagQuotientOfMeasurableBase F i).degree : EReal) -
        (V.flagQuotientOfMeasurableBase F i).majorantDiscrepancy) := by
  calc
    _ = ((V.restrictOfMeasurableBase (F (Fin.last n))).degree : EReal) -
        (V.restrictOfMeasurableBase (F (Fin.last n))).majorantDiscrepancy := by
      rw [htop, V.degree_restrict_top, V.majorantDiscrepancy_restrict_top]
    _ ≤ _ := V.degree_restrict_sub_majorantDiscrepancy_le_sum_flagQuotient
      F hF hzero

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic
public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Dual
import ArakelovGeometry.AdelicVectorBundle.Degree.IsometryDual
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The determinant-discrepancy bound for actual finite flags

The induction uses the genuine two-step dual-degree inequality inside each
restricted bundle and transports both degree and global discrepancy through
canonical nested restrictions. Empty segments and repeated terms are included.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Degree minus global determinant discrepancy is bounded by the sum over
the actual successive quotients of a finite flag starting at zero. -/
theorem degree_restrict_sub_determinantDiscrepancy_le_sum_flagQuotient [S.IsProper]
    (V : AdelicVectorBundle S) {n : ℕ} (F : Fin (n + 1) → Submodule K V)
    (hF : Monotone F) (hzero : F 0 = ⊥)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametric] :
    (V.restrictOfMeasurableBase (F (Fin.last n))).degree -
        (V.restrictOfMeasurableBase (F (Fin.last n))).determinantDiscrepancy ≤
      ∑ i : Fin n, ((V.flagQuotientOfMeasurableBase F i).degree -
        (V.flagQuotientOfMeasurableBase F i).determinantDiscrepancy) := by
  induction n with
  | zero =>
      have hz : F (Fin.last 0) = ⊥ := hzero
      have hr : Module.finrank K (F (Fin.last 0)) = 0 := by
        rw [hz]
        exact finrank_bot K V
      have hd := degree_eq_zero_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (F (Fin.last 0))) hr
      have hδ := determinantDiscrepancy_eq_zero_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (F (Fin.last 0))) hr
      simp only [Fin.sum_univ_zero, hd, hδ, sub_self, le_refl]
  | succ n ih =>
      let G : Fin (n + 1) → Submodule K V := fun i ↦ F i.castSucc
      let U : Submodule K V := F (Fin.last n).castSucc
      let W : Submodule K V := F (Fin.last (n + 1))
      have hG : Monotone G := hF.comp Fin.strictMono_castSucc.monotone
      have hzG : G 0 = ⊥ := hzero
      have hprefix := ih G hG hzG
      change (V.restrictOfMeasurableBase U).degree -
          (V.restrictOfMeasurableBase U).determinantDiscrepancy ≤
        ∑ i : Fin n, ((V.flagQuotientOfMeasurableBase F i.castSucc).degree -
          (V.flagQuotientOfMeasurableBase F i.castSucc).determinantDiscrepancy) at hprefix
      have hUW : U ≤ W := hF (Fin.le_last _)
      have hUWnorm : (V.restrictOfMeasurableBase W).toNormFamily.IsUltrametric := by
        simpa only [restrictOfMeasurableBase_toNormFamily] using hV.restrict W
      have hstep := degree_sub_determinantDiscrepancy_le_restrict_add_quotient
        (V.restrictOfMeasurableBase W) (U.comap W.subtype) (hV := hUWnorm)
      rw [V.degree_restrict_restrict U W hUW,
        V.determinantDiscrepancy_restrict_restrict U W hUW] at hstep
      change (V.restrictOfMeasurableBase W).degree -
          (V.restrictOfMeasurableBase W).determinantDiscrepancy ≤
        ((V.restrictOfMeasurableBase U).degree -
          (V.restrictOfMeasurableBase U).determinantDiscrepancy) +
        ((V.flagQuotientOfMeasurableBase F (Fin.last n)).degree -
          (V.flagQuotientOfMeasurableBase F (Fin.last n)).determinantDiscrepancy) at hstep
      rw [Fin.sum_univ_castSucc]
      exact hstep.trans (add_le_add_left hprefix _)

/-- The full determinant-discrepancy degree bound for a complete actual
finite flag in an ultrametric-outside-infinity bundle. -/
theorem degree_sub_determinantDiscrepancy_le_sum_flagQuotient [S.IsProper]
    (V : AdelicVectorBundle S) {n : ℕ} (F : Fin (n + 1) → Submodule K V)
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametric] :
    V.degree - V.determinantDiscrepancy ≤
      ∑ i : Fin n, ((V.flagQuotientOfMeasurableBase F i).degree -
        (V.flagQuotientOfMeasurableBase F i).determinantDiscrepancy) := by
  calc
    _ = (V.restrictOfMeasurableBase (F (Fin.last n))).degree -
        (V.restrictOfMeasurableBase (F (Fin.last n))).determinantDiscrepancy := by
      rw [htop, V.degree_restrict_top, V.determinantDiscrepancy_restrict_top]
    _ ≤ _ := V.degree_restrict_sub_determinantDiscrepancy_le_sum_flagQuotient
      F hF hzero

end ArakelovGeometry.AdelicVectorBundle

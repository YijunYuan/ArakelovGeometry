/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.DegreeFlag
import ArakelovGeometry.AdelicVectorBundle.DegreeExactSequenceDual
import ArakelovGeometry.AdelicVectorBundle.DegreeIsometryDual

/-!
# The determinant-discrepancy bound for actual finite flags

The induction uses the genuine two-step dual-degree inequality inside each
restricted bundle and transports both degree and global discrepancy through
canonical nested restrictions. Empty segments and repeated terms are included.
-/

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Degree minus global determinant discrepancy is bounded by the sum over
the actual successive quotients of a finite flag starting at zero. -/
theorem degree_restrict_sub_determinantDiscrepancy_le_sum_flagQuotient [S.IsProper]
    (V : AdelicVectorBundle S E) {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (hzero : F 0 = ⊥)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsUltrametric) :
    (V.restrictOfMeasurableBase (F (Fin.last n)) hS).degree hS hN -
        (V.restrictOfMeasurableBase (F (Fin.last n)) hS).determinantDiscrepancy ≤
      ∑ i : Fin n, ((V.flagQuotientOfMeasurableBase F hS i).degree hS hN -
        (V.flagQuotientOfMeasurableBase F hS i).determinantDiscrepancy) := by
  induction n with
  | zero =>
      have hz : F (Fin.last 0) = ⊥ := hzero
      have hr : Module.finrank K (F (Fin.last 0)) = 0 := by
        rw [hz]
        exact finrank_bot K E
      have hd := degree_eq_zero_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (F (Fin.last 0)) hS) hS hN hr
      have hδ := determinantDiscrepancy_eq_zero_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (F (Fin.last 0)) hS) hr
      simp only [Fin.sum_univ_zero, hd, hδ, sub_self, le_refl]
  | succ n ih =>
      let G : Fin (n + 1) → Submodule K E := fun i ↦ F i.castSucc
      let U : Submodule K E := F (Fin.last n).castSucc
      let W : Submodule K E := F (Fin.last (n + 1))
      have hG : Monotone G := hF.comp Fin.strictMono_castSucc.monotone
      have hzG : G 0 = ⊥ := hzero
      have hprefix := ih G hG hzG
      change (V.restrictOfMeasurableBase U hS).degree hS hN -
          (V.restrictOfMeasurableBase U hS).determinantDiscrepancy ≤
        ∑ i : Fin n, ((V.flagQuotientOfMeasurableBase F hS i.castSucc).degree hS hN -
          (V.flagQuotientOfMeasurableBase F hS i.castSucc).determinantDiscrepancy) at hprefix
      have hUW : U ≤ W := hF (Fin.le_last _)
      have hUWnorm : (V.restrictOfMeasurableBase W hS).toNormFamily.IsUltrametric := by
        simpa only [restrictOfMeasurableBase_toNormFamily] using hV.restrict W
      have hstep := degree_sub_determinantDiscrepancy_le_restrict_add_quotient
        (V.restrictOfMeasurableBase W hS) (U.comap W.subtype) hS hN hUWnorm
      rw [V.degree_restrict_restrict U W hUW hS hN,
        V.determinantDiscrepancy_restrict_restrict U W hUW hS hN] at hstep
      change (V.restrictOfMeasurableBase W hS).degree hS hN -
          (V.restrictOfMeasurableBase W hS).determinantDiscrepancy ≤
        ((V.restrictOfMeasurableBase U hS).degree hS hN -
          (V.restrictOfMeasurableBase U hS).determinantDiscrepancy) +
        ((V.flagQuotientOfMeasurableBase F hS (Fin.last n)).degree hS hN -
          (V.flagQuotientOfMeasurableBase F hS (Fin.last n)).determinantDiscrepancy) at hstep
      rw [Fin.sum_univ_castSucc]
      exact hstep.trans (add_le_add_left hprefix _)

/-- The full determinant-discrepancy degree bound for a complete actual
finite flag in an ultrametric-outside-infinity bundle. -/
theorem degree_sub_determinantDiscrepancy_le_sum_flagQuotient [S.IsProper]
    (V : AdelicVectorBundle S E) {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsUltrametric) :
    V.degree hS hN - V.determinantDiscrepancy ≤
      ∑ i : Fin n, ((V.flagQuotientOfMeasurableBase F hS i).degree hS hN -
        (V.flagQuotientOfMeasurableBase F hS i).determinantDiscrepancy) := by
  calc
    _ = (V.restrictOfMeasurableBase (F (Fin.last n)) hS).degree hS hN -
        (V.restrictOfMeasurableBase (F (Fin.last n)) hS).determinantDiscrepancy := by
      rw [htop, V.degree_restrict_top hS hN, V.determinantDiscrepancy_restrict_top hS hN]
    _ ≤ _ := V.degree_restrict_sub_determinantDiscrepancy_le_sum_flagQuotient
      F hF hzero hS hN hV

end ArakelovGeometry.AdelicVectorBundle

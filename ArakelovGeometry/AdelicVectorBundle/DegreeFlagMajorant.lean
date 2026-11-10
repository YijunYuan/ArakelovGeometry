/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.DegreeFlag
import ArakelovGeometry.AdelicVectorBundle.DegreeExactSequenceMajorant
import ArakelovGeometry.AdelicVectorBundle.MajorantDiscrepancyIsometry

/-!
# The capital-discrepancy degree bound for actual finite flags

The genuine two-step majorant bound applies in each restricted bundle.
Canonical nested restrictions preserve degree and the actual majorant
infimum. Extended-real inequalities include infinite global discrepancies,
empty segments, and repeated terms of the flag.
-/

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Degree minus the actual global capital discrepancy is bounded by the
sum over the actual successive quotients of every finite flag starting at zero.
The terms are extended real, so infinite discrepancies are retained. -/
theorem degree_restrict_sub_majorantDiscrepancy_le_sum_flagQuotient [S.IsProper]
    (V : AdelicVectorBundle S E) {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (hzero : F 0 = ⊥)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.restrictOfMeasurableBase (F (Fin.last n)) hS).degree hS hN : EReal) -
        (V.restrictOfMeasurableBase (F (Fin.last n)) hS).majorantDiscrepancy hN ≤
      ∑ i : Fin n, (((V.flagQuotientOfMeasurableBase F hS i).degree hS hN : EReal) -
        (V.flagQuotientOfMeasurableBase F hS i).majorantDiscrepancy hN) := by
  induction n with
  | zero =>
      have hz : F (Fin.last 0) = ⊥ := hzero
      have hr : Module.finrank K (F (Fin.last 0)) = 0 := by
        rw [hz]
        exact finrank_bot K E
      have hd := degree_eq_zero_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (F (Fin.last 0)) hS) hS hN hr
      have hΔ := majorantDiscrepancy_eq_zero_of_finrank_eq_zero
        (V.restrictOfMeasurableBase (F (Fin.last 0)) hS) hN hr
      simp only [Fin.sum_univ_zero, hd, hΔ, EReal.coe_zero, sub_zero, le_refl]
  | succ n ih =>
      let G : Fin (n + 1) → Submodule K E := fun i ↦ F i.castSucc
      let U : Submodule K E := F (Fin.last n).castSucc
      let W : Submodule K E := F (Fin.last (n + 1))
      have hG : Monotone G := hF.comp Fin.strictMono_castSucc.monotone
      have hzG : G 0 = ⊥ := hzero
      have hprefix := ih G hG hzG
      change ((V.restrictOfMeasurableBase U hS).degree hS hN : EReal) -
          (V.restrictOfMeasurableBase U hS).majorantDiscrepancy hN ≤
        ∑ i : Fin n,
          (((V.flagQuotientOfMeasurableBase F hS i.castSucc).degree hS hN : EReal) -
          (V.flagQuotientOfMeasurableBase F hS i.castSucc).majorantDiscrepancy hN) at hprefix
      have hUW : U ≤ W := hF (Fin.le_last _)
      have hstep := degree_sub_majorantDiscrepancy_le_restrict_add_quotient
        (V.restrictOfMeasurableBase W hS) (U.comap W.subtype) hS hN
      rw [V.degree_restrict_restrict U W hUW hS hN,
        V.majorantDiscrepancy_restrict_restrict U W hUW hS hN] at hstep
      change ((V.restrictOfMeasurableBase W hS).degree hS hN : EReal) -
          (V.restrictOfMeasurableBase W hS).majorantDiscrepancy hN ≤
        (((V.restrictOfMeasurableBase U hS).degree hS hN : EReal) -
          (V.restrictOfMeasurableBase U hS).majorantDiscrepancy hN) +
        (((V.flagQuotientOfMeasurableBase F hS (Fin.last n)).degree hS hN : EReal) -
          (V.flagQuotientOfMeasurableBase F hS (Fin.last n)).majorantDiscrepancy hN) at hstep
      rw [Fin.sum_univ_castSucc]
      exact hstep.trans (add_le_add_left hprefix _)

/-- Source equation (4.27) for every complete actual finite flag. No original
ultrametricity or finiteness of the global majorant discrepancies is assumed. -/
theorem degree_sub_majorantDiscrepancy_le_sum_flagQuotient [S.IsProper]
    (V : AdelicVectorBundle S E) {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.degree hS hN : EReal) - V.majorantDiscrepancy hN ≤
      ∑ i : Fin n, (((V.flagQuotientOfMeasurableBase F hS i).degree hS hN : EReal) -
        (V.flagQuotientOfMeasurableBase F hS i).majorantDiscrepancy hN) := by
  calc
    _ = ((V.restrictOfMeasurableBase (F (Fin.last n)) hS).degree hS hN : EReal) -
        (V.restrictOfMeasurableBase (F (Fin.last n)) hS).majorantDiscrepancy hN := by
      rw [htop, V.degree_restrict_top hS hN, V.majorantDiscrepancy_restrict_top hS hN]
    _ ≤ _ := V.degree_restrict_sub_majorantDiscrepancy_le_sum_flagQuotient
      F hF hzero hS hN

end ArakelovGeometry.AdelicVectorBundle

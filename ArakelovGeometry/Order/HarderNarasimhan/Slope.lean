/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.NashEquilibrium
public import HarderNarasimhan.PayoffFunction.Semistable.Breakpoints
public import HarderNarasimhan.PayoffFunction.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Supermodular slopes as Harder–Narasimhan games

Breakpoints of the upstream game give largest slope maximizers.
Modular ranks and supermodular degrees supply the slope and convexity axioms.
-/

@[expose] public section

open HarderNarasimhan
open scoped NNReal

namespace HarderNarasimhan.PayoffFunction

section ChainConditions

variable {L C : Type*} [PartialOrder L] [CompleteLattice C]

/-- A well-founded strict order excludes the decreasing chains in `ADCC`. -/
theorem adcc_of_wellFoundedLT [WellFoundedLT L] (μ : PayoffFunction L C) : μ.ADCC :=
  ⟨fun _ f _ hf ↦ (not_strictAnti_of_wellFoundedLT f hf).elim⟩

/-- A well-founded strict order also implies the strong descending chain condition. -/
theorem strongDCC_of_wellFoundedLT [Nontrivial L] [BoundedOrder L] [WellFoundedLT L]
    (μ : PayoffFunction L C) : μ.StrongDCC :=
  ⟨fun f hf ↦ (not_strictAnti_of_wellFoundedLT f hf).elim⟩

end ChainConditions

section Maximizer

variable {L C : Type*} [Nontrivial L] [Lattice L] [BoundedOrder L]
  [WellFoundedLT L] [WellFoundedGT L] [CompleteLinearOrder C]
  {μ : PayoffFunction L C} [μ.IsSlopeLike]

/-- A breakpoint of a slope-like payoff is the largest initial segment
maximizing the original payoff, not just the game value. -/
theorem IsBreakpoint.isGreatest_initialPayoff {D : L} (hD : μ.IsBreakpoint ⊤ D) :
    ∀ F : L, (hF : ⊥ < F) →
      μ ⟨⊥, F, hF⟩ ≤ μ ⟨⊥, D, hD.left_lt⟩ ∧
      (μ ⟨⊥, F, hF⟩ = μ ⟨⊥, D, hD.left_lt⟩ → F ≤ D) := by
  let hsl : μ.IsSlopeLike := inferInstance
  let : μ.StrongDCC := strongDCC_of_wellFoundedLT μ
  have hBA : μ.B ⊤ ≤ μ.A ⟨⊥, D, hD.left_lt⟩ := by
    apply B_le
    intro F hF
    rw [hsl.min_eq_A]
    exact le_of_not_gt (hD.not_lt F (StrictIntvl.mem_top F) hF.1.ne)
  have hAD : μ.A ⟨⊥, D, hD.left_lt⟩ = μ ⟨⊥, D, hD.left_lt⟩ := by
    apply le_antisymm
    · rw [← hsl.min_eq_A]
      exact min_le_apply
    · exact (le_max (I := ⊤) ⟨hD.left_lt, le_top⟩).trans
        ((B_top_eq_max_top (μ := μ)).symm.le.trans hBA)
  have hmax : ∀ F : L, (hF : ⊥ < F) → μ ⟨⊥, F, hF⟩ ≤ μ ⟨⊥, D, hD.left_lt⟩ := by
    intro F hF
    exact (le_max (I := ⊤) ⟨hF, le_top⟩).trans
      ((B_top_eq_max_top (μ := μ)).symm.le.trans (hBA.trans_eq hAD))
  intro F hF
  refine ⟨hmax F hF, fun he ↦ ?_⟩
  let I : StrictIntvl L := ⟨⊥, F, hF⟩
  have hmaxF : μ.max I = μ I := by
    apply le_antisymm _ apply_le_max
    apply max_le
    intro G hG
    exact (hmax G hG.1).trans_eq he.symm
  have hminF : μ.min I = μ I := by
    have h := (max_top_eq_apply_iff (μ := μ.restrict I)).mp (by
      simpa only [max_restrict_apply, restrict_apply, StrictIntvl.ofSub_top] using hmaxF)
    have h' : μ.min I = μ.max I := by
      simpa only [min_restrict_apply, max_restrict_apply, StrictIntvl.ofSub_top] using h
    exact h'.trans hmaxF
  apply hD.le_of_eq F (StrictIntvl.mem_top F) hF.ne
  exact (hsl.min_eq_A I).symm.trans (hminF.trans (he.trans hAD.symm))

/-- Convex slope-like payoffs on a lattice with both chain conditions have
a largest initial-payoff maximizer. -/
theorem exists_largest_initialPayoff [μ.IsConvex] :
    ∃ (D : L) (hD : ⊥ < D), ∀ (F : L) (hF : ⊥ < F),
      μ ⟨⊥, F, hF⟩ ≤ μ ⟨⊥, D, hD⟩ ∧
      (μ ⟨⊥, F, hF⟩ = μ ⟨⊥, D, hD⟩ → F ≤ D) := by
  let : μ.ADCC := adcc_of_wellFoundedLT μ
  obtain ⟨D, hD⟩ := breakpoints_nonempty (μ := μ) (I := ⊤) inferInstance
  exact ⟨D, hD.left_lt, hD.isGreatest_initialPayoff⟩

end Maximizer

end HarderNarasimhan.PayoffFunction

namespace ArakelovGeometry

section RankDegree

variable {L : Type*} [PartialOrder L]

/-- The positive increment of a strictly increasing rank on a strict interval. -/
def intervalRank (r : L → ℝ) (hr : StrictMono r) (I : StrictIntvl L) : ℝ≥0 :=
  ⟨r I.right - r I.left, sub_nonneg.mpr (hr I.lt).le⟩

theorem intervalRank_pos (r : L → ℝ) (hr : StrictMono r) (I : StrictIntvl L) :
    0 < intervalRank r hr I := sub_pos.mpr (hr I.lt)

/-- The slope game of endpoint differences of rank and degree. -/
noncomputable def rankDegreePayoff (r d : L → ℝ) (hr : StrictMono r) :
    PayoffFunction L (DedekindCut ℝ) :=
  PayoffFunction.slope (intervalRank r hr) (fun I ↦ d I.right - d I.left)

theorem rankDegreePayoff_apply (r d : L → ℝ) (hr : StrictMono r) (I : StrictIntvl L) :
    rankDegreePayoff r d hr I =
      DedekindCut.principal ((d I.right - d I.left) / (r I.right - r I.left)) := by
  simp only [rankDegreePayoff, PayoffFunction.slope, PayoffFunction.coe_mk,
    intervalRank_pos, ↓reduceDIte]
  congr 1
  change (r I.right - r I.left)⁻¹ * (d I.right - d I.left) = _
  rw [div_eq_mul_inv, mul_comm]

/-- Additivity of endpoint differences supplies slope-likeness through the upstream theorem. -/
theorem isSlopeLike_rankDegreePayoff (r d : L → ℝ) (hr : StrictMono r) :
    (rankDegreePayoff r d hr).IsSlopeLike := by
  apply PayoffFunction.isSlopeLike_slope
  · intro x y z hxy hyz
    dsimp
    ring
  · intro x y z hxy hyz
    apply NNReal.eq
    change r z - r x = (r y - r x) + (r z - r y)
    ring
  · intro x y hxy hzero
    exact ((intervalRank_pos r hr ⟨x, y, hxy⟩).ne' hzero).elim

end RankDegree

section Lattice

variable {L : Type*} [Lattice L]

/-- Modularity of rank and supermodularity of degree give game convexity. -/
theorem isConvex_rankDegreePayoff (r d : L → ℝ) (hr : StrictMono r)
    (hrmod : ∀ U W, r (U ⊓ W) + r (U ⊔ W) = r U + r W)
    (hdsuper : ∀ U W, d U + d W ≤ d (U ⊓ W) + d (U ⊔ W)) :
    (rankDegreePayoff r d hr).IsConvex := by
  constructor
  intro U W hUW
  simp only [rankDegreePayoff_apply, DedekindCut.principal_le_principal]
  have he : r U - r (U ⊓ W) = r (U ⊔ W) - r W := by
    have := hrmod U W
    linarith
  rw [he]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr (hr.monotone le_sup_right))
  have := hdsuper U W
  linarith

end Lattice

end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic
public import ArakelovGeometry.AdelicVectorBundle.Slope.Subquotient

/-!
# Slope bounds for finite flags

The extension inequality bounds the minimal slope of every initial flag term.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]

/-- The actual extension minimum bound for two nested ambient restrictions. -/
theorem min_minimalSlope_restrict_le_of_le (A B : Submodule K V) (hAB : A ≤ B) :
    min ((V.restrictOfNormMeasurability A).minimalSlope)
      (((V.restrictOfNormMeasurability B).quotientOfNormMeasurability
        (A.comap B.subtype)).minimalSlope) ≤
    (V.restrictOfNormMeasurability B).minimalSlope := by
  have h := min_minimalSlope_restrict_le_minimalSlope_preimage
    (V.restrictOfNormMeasurability B) (A.comap B.subtype) ⊤
  simp only [Submodule.comap_top] at h
  rw [((V.restrictOfNormMeasurability B).quotientOfNormMeasurability
    (A.comap B.subtype)).minimalSlope_restrict_top,
    (V.restrictOfNormMeasurability B).minimalSlope_restrict_top] at h
  rw [V.minimalSlope_restrict_restrict A B hAB] at h
  exact h

/-- Decreasing actual factor minima bound every nonzero initial flag term. -/
theorem le_minimalSlope_restrict_flag_of_factor_minima {n : ℕ}
    (U : Fin (n + 1) → Submodule K V) (b : Fin n → ℝ)
    (hU : Monotone U) (hz : U 0 = ⊥) (hb : Antitone b)
    (hQ : ∀ i, (b i : EReal) ≤
      (V.flagQuotientOfNormMeasurability U i).minimalSlope) :
    ∀ i : Fin n, (b i : EReal) ≤
      (V.restrictOfNormMeasurability (U i.succ)).minimalSlope := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    intro i
    induction i using Fin.induction with
    | zero =>
      have he := min_minimalSlope_restrict_le_of_le V (U 0) (U (0 : Fin (n + 1)).succ)
        (hU (Fin.zero_le _))
      rw [hz] at he
      have hm := minimalSlope_eq_top_of_finrank_eq_zero
        (V.restrictOfNormMeasurability (⊥ : Submodule K V)) (finrank_bot K V)
      rw [hm, min_top_left] at he
      have hq := hQ 0
      change (b 0 : EReal) ≤ minimalSlope
        (quotientOfNormMeasurability (V.restrictOfNormMeasurability (U (0 : Fin (n + 1)).succ))
          ((U 0).comap (U (0 : Fin (n + 1)).succ).subtype)) at hq
      rw [hz] at hq
      exact hq.trans he
    | succ i ih =>
      have he := min_minimalSlope_restrict_le_of_le V (U i.succ.castSucc) (U i.succ.succ)
        (hU i.succ.castSucc_lt_succ.le)
      have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext (by rfl)
      rw [hi] at ih
      have hb' : (b i.succ : EReal) ≤ b i.castSucc := EReal.coe_le_coe
        (hb i.castSucc_lt_succ.le)
      exact (le_min (hb'.trans ih) (hQ i.succ)).trans he

end

end ArakelovGeometry.AdelicVectorBundle

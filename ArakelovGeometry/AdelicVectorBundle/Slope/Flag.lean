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

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

/-- The actual extension minimum bound for two nested ambient restrictions. -/
theorem min_minimalSlope_restrict_le_of_le (A B : Submodule K E) (hAB : A ≤ B) :
    min ((V.restrictOfMeasurableBase A).minimalSlope)
      (((V.restrictOfMeasurableBase B).quotientOfMeasurableBase
        (A.comap B.subtype)).minimalSlope) ≤
    (V.restrictOfMeasurableBase B).minimalSlope := by
  have h := min_minimalSlope_restrict_le_minimalSlope_preimage
    (V.restrictOfMeasurableBase B) (A.comap B.subtype) ⊤
  simp only [Submodule.comap_top, minimalSlope_restrict_top] at h
  rw [V.minimalSlope_restrict_restrict A B hAB] at h
  exact h

/-- Decreasing actual factor minima bound every nonzero initial flag term. -/
theorem le_minimalSlope_restrict_flag_of_factor_minima {n : ℕ}
    (U : Fin (n + 1) → Submodule K E) (b : Fin n → ℝ)
    (hU : Monotone U) (hz : U 0 = ⊥) (hb : Antitone b)
    (hQ : ∀ i, (b i : EReal) ≤
      (V.flagQuotientOfMeasurableBase U i).minimalSlope) :
    ∀ i : Fin n, (b i : EReal) ≤
      (V.restrictOfMeasurableBase (U i.succ)).minimalSlope := by
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
        (V.restrictOfMeasurableBase (⊥ : Submodule K E)) (finrank_bot K E)
      rw [hm, min_top_left] at he
      have hq := hQ 0
      change (b 0 : EReal) ≤ minimalSlope
        (quotientOfMeasurableBase (V.restrictOfMeasurableBase (U (0 : Fin (n + 1)).succ))
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

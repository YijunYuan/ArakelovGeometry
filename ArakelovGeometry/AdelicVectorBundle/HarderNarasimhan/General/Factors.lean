/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Game

/-!
# Actual factors of general HN filtrations

The general game supplies a finite strict flag whose actual quotient factors are
semistable. Their modified means and minimal slopes are the jumps of the
original real-indexed filtration.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]


/-- Produce the actual strict general HN flag with semistable actual factors,
whose genuine modified means and minima are its strictly decreasing jumps.
No flag, factor semistability, or completed norm identity is assumed. -/
theorem exists_hnFlag_semistable_factors :
    ∃ (n : ℕ) (U : Fin (n + 1) → Submodule K V) (b : Fin n → ℝ),
    StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧ StrictAnti b ∧
      (∀ t, V.hnFiltration t = ⨆ (i : Fin n) (_ : t ≤ b i), U i.succ) ∧
      (∀ i : Fin n, (V.flagQuotientOfNormMeasurability U i).IsSemistable ∧
        (V.flagQuotientOfNormMeasurability U i).minimalSlope = (b i : EReal) ∧
        (V.flagQuotientOfNormMeasurability U i).hnMeanSlope = b i) := by
  obtain ⟨⟨n, U⟩, ⟨hU, hz, ht, hsemi, hb⟩, _⟩ := V.existsUnique_hnFlag
  refine ⟨n, U, (fun i ↦ (V.flagQuotientOfNormMeasurability U i).hnMeanSlope),
    hU, hz, ht, hb, ?_, ?_⟩
  · exact fun t ↦ V.hnFiltration_eq_of_semistableFlag U hU hz ht (hsemi := hsemi) hb t
  · intro i
    exact ⟨hsemi i,
      ((V.flagQuotientOfNormMeasurability U i).isSemistable_iff_hnMeanSlope_eq_minimalSlope
        (hsemi i).1).mp (hsemi i) |>.symm, rfl⟩

end

end ArakelovGeometry.AdelicVectorBundle

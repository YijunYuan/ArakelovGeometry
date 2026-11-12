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

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]


/-- Produce the actual strict general HN flag with semistable actual factors,
whose genuine modified means and minima are its strictly decreasing jumps.
No flag, factor semistability, or completed norm identity is assumed. -/
theorem exists_generalHNFlag_semistable_factors :
    ∃ (n : ℕ) (U : Fin (n + 1) → Submodule K E) (b : Fin n → ℝ),
    StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧ StrictAnti b ∧
      (∀ t, V.generalHNFiltration t = ⨆ (i : Fin n) (_ : t ≤ b i), U i.succ) ∧
      (∀ i : Fin n, (V.flagQuotientOfMeasurableBase U i).IsSemistable ∧
        (V.flagQuotientOfMeasurableBase U i).minimalSlope = (b i : EReal) ∧
        (V.flagQuotientOfMeasurableBase U i).modifiedSlope = b i) := by
  obtain ⟨⟨n, U⟩, ⟨hU, hz, ht, hsemi, hb⟩, _⟩ := V.existsUnique_generalHNFlag
  refine ⟨n, U, (fun i ↦ (V.flagQuotientOfMeasurableBase U i).modifiedSlope),
    hU, hz, ht, hb, ?_, ?_⟩
  · exact fun t ↦ V.generalHNFiltration_eq_of_semistableFlag U hU hz ht (hsemi := hsemi) hb t
  · intro i
    exact ⟨hsemi i,
      ((V.flagQuotientOfMeasurableBase U i).isSemistable_iff_modifiedSlope_eq_minimalSlope
        (hsemi i).1).mp (hsemi i) |>.symm, rfl⟩

end

end ArakelovGeometry.AdelicVectorBundle

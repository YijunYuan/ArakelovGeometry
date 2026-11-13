/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Game

/-!
# Uniqueness of actual general HN flags

The imported general game proves unique finite flag existence and reconstructs the
original filtration from any semistable decreasing flag. Here every candidate term
is attained, and the complete filtration range is identified with the flag range.
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


/-- Every candidate term is attained at its actual factor modified mean. -/
theorem semistableFlag_succ_eq_hnFiltration {n : ℕ}
    (U : Fin (n + 1) → Submodule K V) (hU : StrictMono U) (hz : U 0 = ⊥)
    (ht : U (Fin.last n) = ⊤)
    [hsemi : ∀ i : Fin n, (V.flagQuotientOfNormMeasurability U i).IsSemistable]
    (hb : StrictAnti (fun i : Fin n ↦ (V.flagQuotientOfNormMeasurability U i).hnMeanSlope
)) (i : Fin n) :
    V.hnFiltration
      ((V.flagQuotientOfNormMeasurability U i).hnMeanSlope) = U i.succ := by
  rw [V.hnFiltration_eq_of_semistableFlag U hU hz ht hb]
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro hij
    have hji : j ≤ i := by
      by_contra hn
      exact (not_le_of_gt (hb (lt_of_not_ge hn))) hij
    exact hU.monotone (show j.succ ≤ i.succ by
      change j.val + 1 ≤ i.val + 1
      exact Nat.add_le_add_right hji 1)
  · exact le_iSup_of_le i (le_iSup_of_le le_rfl le_rfl)

/-- The complete actual filtration levels are exactly the candidate flag terms. -/
theorem range_hnFiltration_eq_of_semistableFlag {n : ℕ}
    (U : Fin (n + 1) → Submodule K V) (hU : StrictMono U) (hz : U 0 = ⊥)
    (ht : U (Fin.last n) = ⊤)
    [hsemi : ∀ i : Fin n, (V.flagQuotientOfNormMeasurability U i).IsSemistable]
    (hb : StrictAnti (fun i : Fin n ↦ (V.flagQuotientOfNormMeasurability U i).hnMeanSlope
)) :
    Set.range (V.hnFiltration) = Set.range U := by
  classical
  let b : Fin n → ℝ := fun i ↦ (V.flagQuotientOfNormMeasurability U i).hnMeanSlope
  apply Set.Subset.antisymm
  · rintro W ⟨t, rfl⟩
    let J : Finset (Fin n) := Finset.univ.filter (fun i ↦ t ≤ b i)
    by_cases hJ : J.Nonempty
    · let i := J.max' hJ
      have hi : t ≤ b i := (Finset.mem_filter.mp (Finset.max'_mem J hJ)).2
      refine ⟨i.succ, ?_⟩
      symm
      rw [V.hnFiltration_eq_of_semistableFlag U hU hz ht hb]
      apply le_antisymm
      · apply iSup_le
        intro j
        apply iSup_le
        intro hj
        have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
        have hji := Finset.le_max' J j hjJ
        exact hU.monotone (show j.succ ≤ i.succ by
          change j.val + 1 ≤ i.val + 1
          exact Nat.add_le_add_right hji 1)
      · exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
    · refine ⟨0, ?_⟩
      rw [hz, V.hnFiltration_eq_of_semistableFlag U hU hz ht hb]
      symm
      apply le_antisymm _ bot_le
      apply iSup_le
      intro i
      apply iSup_le
      intro hi
      exact (hJ ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩).elim
  · rintro W ⟨k, rfl⟩
    by_cases hk : k.val = 0
    · obtain ⟨t, ht⟩ := V.exists_hnFiltration_eq_bot
      refine ⟨t, ?_⟩
      rw [show k = 0 from Fin.ext hk, hz]
      exact ht
    · let i : Fin n := ⟨k.val - 1, by have h := k.isLt; omega⟩
      have hik : i.succ = k := Fin.ext (by dsimp [i]; omega)
      exact ⟨b i, (V.semistableFlag_succ_eq_hnFiltration
        U hU hz ht hb i).trans (congrArg U hik)⟩


end

end ArakelovGeometry.AdelicVectorBundle

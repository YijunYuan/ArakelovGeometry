/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Ordered

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Restriction
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.SemistableFlagDegree
import ArakelovGeometry.LinearAlgebra.FiniteFiltration
import ArakelovGeometry.LinearAlgebra.FiniteFlagRanks
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The actual finite flag of a general minimal-slope filtration

The actual filtration supplies the complete strict flag and its real jumps.
Actual ordered rank cuts identify the jump on each rank block, with the
actual canonical quotient rank as its multiplicity.
-/

@[expose] public section

open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]

/-- Extract the actual complete strict flag and all its jump data from
the produced general filtration. No finite flag or finite image is given. -/
theorem exists_hnFlag_and_jumps :
    ∃ (n : ℕ) (U : Fin (n + 1) → Submodule K V) (b : Fin n → ℝ),
      StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧
      Set.range U = Set.range (V.hnFiltration) ∧ StrictAnti b ∧
      (∀ i t, U i.succ ≤ V.hnFiltration t ↔ t ≤ b i) ∧
      (∀ i, V.hnFiltration (b i) = U i.succ) ∧
      (∀ i, (⨆ s : {s : ℝ // b i < s}, V.hnFiltration s.val) = U i.castSucc) ∧
      (∀ t, V.hnFiltration t = ⨆ (i : Fin n) (_ : t ≤ b i), U i.succ) := by
  apply Submodule.exists_strictMono_flag_and_jumps_of_antitone
    (V.antitone_hnFiltration)
    (V.exists_hnFiltration_eq_bot)
    (V.exists_hnFiltration_eq_top)
  intro t
  obtain ⟨δ, hδ, hc⟩ := V.hnFiltration_locallyConstant_left t
  refine ⟨δ, hδ, fun s hs hst ↦ ?_⟩
  have he : t - (t - s) = s := by ring
  have h := hc (t - s) (sub_nonneg.mpr hst) (by linarith)
  rwa [he] at h

private theorem hnSlope_eq_jump_of_rank_interval {n : ℕ}
    (U : Fin (n + 1) → Submodule K V) (b : Fin n → ℝ) (hU : StrictMono U)
    (hrange : Set.range U = Set.range (V.hnFiltration))
    (hcut : ∀ i t, U i.succ ≤ V.hnFiltration t ↔ t ≤ b i)
    (hat : ∀ i, V.hnFiltration (b i) = U i.succ)
    (i : Fin n) (j : Fin (Module.finrank K V))
    (hlo : Module.finrank K (U i.castSucc) ≤ j.val)
    (hhi : j.val < Module.finrank K (U i.succ)) :
    V.hnSlope j = b i := by
  apply le_antisymm
  · let μ := V.hnSlope j
    obtain ⟨k, hk⟩ : V.hnFiltration μ ∈ Set.range U := by
      rw [hrange]
      exact ⟨μ, rfl⟩
    have hp := V.lt_finrank_hnFiltration_orderedSlope j
    change j.val < Module.finrank K (V.hnFiltration μ) at hp
    rw [← hk] at hp
    have hik : i.succ ≤ k := by
      by_contra h
      have hki : k ≤ i.castSucc := by
        change ¬ i.val + 1 ≤ k.val at h
        change k.val ≤ i.val
        omega
      have hd := Submodule.finrank_mono (hU.monotone hki)
      omega
    exact (hcut i μ).mp ((hU.monotone hik).trans (le_of_eq hk))
  · apply (V.le_hnSlope_iff_lt_filtration_finrank (b i) j).mpr
    rwa [hat i]

/-- Produce an actual complete strict general filtration flag together
with its genuine rank-block slopes, nonzero term minima, and every real
test-function weighted sum using canonical actual quotient ranks. -/
theorem exists_hnFlag_orderedSlope_sum :
    ∃ (n : ℕ) (U : Fin (n + 1) → Submodule K V) (b : Fin n → ℝ),
      StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧
      Set.range U = Set.range (V.hnFiltration) ∧ StrictAnti b ∧
      (∀ i t, U i.succ ≤ V.hnFiltration t ↔ t ≤ b i) ∧
      (∀ i, V.hnFiltration (b i) = U i.succ) ∧
      (∀ i, (⨆ s : {s : ℝ // b i < s}, V.hnFiltration s.val) = U i.castSucc) ∧
      (∀ t, V.hnFiltration t = ⨆ (i : Fin n) (_ : t ≤ b i), U i.succ) ∧
      (∀ (i : Fin n) (j : Fin (Module.finrank K V)),
        Module.finrank K (U i.castSucc) ≤ j.val →
        j.val < Module.finrank K (U i.succ) → V.hnSlope j = b i) ∧
      (∀ i, (V.restrictOfNormMeasurability (U i.succ)).minimalSlope = (b i : EReal)) ∧
      (∀ f : ℝ → ℝ,
        (∑ j, f (V.hnSlope j)) =
          ∑ i : Fin n, (Module.finrank K
            ((U i.succ) ⧸ ((U i.castSucc).comap (U i.succ).subtype)) : ℝ) * f (b i)) := by
  obtain ⟨n, U, b, hU, hz, ht, hrange, hb, hcut, hat, hright, hrec⟩ :=
    V.exists_hnFlag_and_jumps
  have hblock := V.hnSlope_eq_jump_of_rank_interval U b hU
    hrange hcut hat
  have hmin : ∀ i, (V.restrictOfNormMeasurability (U i.succ)).minimalSlope =
      (b i : EReal) := by
    intro i
    have hstep := Submodule.finrank_lt_finrank_of_lt (hU i.castSucc_lt_succ)
    let j : Fin (Module.finrank K V) :=
      ⟨Module.finrank K (U i.castSucc), hstep.trans_le (U i.succ).finrank_le⟩
    have he := hblock i j le_rfl hstep
    have hm := V.minimalSlope_restrict_hnFiltration_orderedSlope j
    rwa [he, hat i] at hm
  refine ⟨n, U, b, hU, hz, ht, hrange, hb, hcut, hat, hright, hrec, hblock, hmin, ?_⟩
  intro f
  have hs := Submodule.sum_eq_sum_flag_rank_blocks U hU.monotone hz ht
    (fun j ↦ f (V.hnSlope j)) (fun i ↦ f (b i))
    (fun i j hlo hhi ↦ congrArg f (hblock i j hlo hhi))
  simpa only [ArakelovGeometry.finrank_flagQuotient_eq_sub U hU.monotone] using hs

end

end ArakelovGeometry.AdelicVectorBundle

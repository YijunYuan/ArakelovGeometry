/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeFlag
public import ArakelovGeometry.AdelicVectorBundle.GeneralHNRestriction
public import ArakelovGeometry.AdelicVectorBundle.SemistableFlagDegree
public import ArakelovGeometry.LinearAlgebra.FiniteFiltration
public import ArakelovGeometry.LinearAlgebra.FiniteFlagRanks

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

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- Extract the actual complete strict flag and all its jump data from
the produced general filtration. No finite flag or finite image is given. -/
theorem exists_generalHNFlag_and_jumps :
    ∃ (n : ℕ) (U : Fin (n + 1) → Submodule K E) (b : Fin n → ℝ),
      StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧
      Set.range U = Set.range (V.generalHNFiltration hS hN) ∧ StrictAnti b ∧
      (∀ i t, U i.succ ≤ V.generalHNFiltration hS hN t ↔ t ≤ b i) ∧
      (∀ i, V.generalHNFiltration hS hN (b i) = U i.succ) ∧
      (∀ i, (⨆ s : {s : ℝ // b i < s}, V.generalHNFiltration hS hN s.val) = U i.castSucc) ∧
      (∀ t, V.generalHNFiltration hS hN t = ⨆ (i : Fin n) (_ : t ≤ b i), U i.succ) := by
  apply Submodule.exists_strictMono_flag_and_jumps_of_antitone
    (V.antitone_generalHNFiltration hS hN)
    (V.exists_generalHNFiltration_eq_bot hS hN)
    (V.exists_generalHNFiltration_eq_top hS hN)
  intro t
  obtain ⟨δ, hδ, hc⟩ := V.generalHNFiltration_locallyConstant_left hS hN t
  refine ⟨δ, hδ, fun s hs hst ↦ ?_⟩
  have he : t - (t - s) = s := by ring
  have h := hc (t - s) (sub_nonneg.mpr hst) (by linarith)
  rwa [he] at h

private theorem generalHNOrderedSlope_eq_jump_of_rank_interval {n : ℕ}
    (U : Fin (n + 1) → Submodule K E) (b : Fin n → ℝ) (hU : StrictMono U)
    (hrange : Set.range U = Set.range (V.generalHNFiltration hS hN))
    (hcut : ∀ i t, U i.succ ≤ V.generalHNFiltration hS hN t ↔ t ≤ b i)
    (hat : ∀ i, V.generalHNFiltration hS hN (b i) = U i.succ)
    (i : Fin n) (j : Fin (Module.finrank K E))
    (hlo : Module.finrank K (U i.castSucc) ≤ j.val)
    (hhi : j.val < Module.finrank K (U i.succ)) :
    V.generalHNOrderedSlope hS hN j = b i := by
  apply le_antisymm
  · let μ := V.generalHNOrderedSlope hS hN j
    obtain ⟨k, hk⟩ : V.generalHNFiltration hS hN μ ∈ Set.range U := by
      rw [hrange]
      exact ⟨μ, rfl⟩
    have hp := V.lt_finrank_generalHNFiltration_orderedSlope hS hN j
    change j.val < Module.finrank K (V.generalHNFiltration hS hN μ) at hp
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
  · apply (V.le_generalHNOrderedSlope_iff_lt_filtration_finrank hS hN (b i) j).mpr
    rwa [hat i]

/-- Produce an actual complete strict general filtration flag together
with its genuine rank-block slopes, nonzero term minima, and every real
test-function weighted sum using canonical actual quotient ranks. -/
theorem exists_generalHNFlag_orderedSlope_sum :
    ∃ (n : ℕ) (U : Fin (n + 1) → Submodule K E) (b : Fin n → ℝ),
      StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧
      Set.range U = Set.range (V.generalHNFiltration hS hN) ∧ StrictAnti b ∧
      (∀ i t, U i.succ ≤ V.generalHNFiltration hS hN t ↔ t ≤ b i) ∧
      (∀ i, V.generalHNFiltration hS hN (b i) = U i.succ) ∧
      (∀ i, (⨆ s : {s : ℝ // b i < s}, V.generalHNFiltration hS hN s.val) = U i.castSucc) ∧
      (∀ t, V.generalHNFiltration hS hN t = ⨆ (i : Fin n) (_ : t ≤ b i), U i.succ) ∧
      (∀ (i : Fin n) (j : Fin (Module.finrank K E)),
        Module.finrank K (U i.castSucc) ≤ j.val →
        j.val < Module.finrank K (U i.succ) → V.generalHNOrderedSlope hS hN j = b i) ∧
      (∀ i, (V.restrictOfMeasurableBase (U i.succ) hS).minimalSlope hS hN = (b i : EReal)) ∧
      (∀ f : ℝ → ℝ,
        (∑ j, f (V.generalHNOrderedSlope hS hN j)) =
          ∑ i : Fin n, (Module.finrank K
            ((U i.succ) ⧸ ((U i.castSucc).comap (U i.succ).subtype)) : ℝ) * f (b i)) := by
  obtain ⟨n, U, b, hU, hz, ht, hrange, hb, hcut, hat, hright, hrec⟩ :=
    V.exists_generalHNFlag_and_jumps hS hN
  have hblock := V.generalHNOrderedSlope_eq_jump_of_rank_interval hS hN U b hU
    hrange hcut hat
  have hmin : ∀ i, (V.restrictOfMeasurableBase (U i.succ) hS).minimalSlope hS hN =
      (b i : EReal) := by
    intro i
    have hstep := Submodule.finrank_lt_finrank_of_lt (hU i.castSucc_lt_succ)
    let j : Fin (Module.finrank K E) :=
      ⟨Module.finrank K (U i.castSucc), hstep.trans_le (U i.succ).finrank_le⟩
    have he := hblock i j le_rfl hstep
    have hm := V.minimalSlope_restrict_generalHNFiltration_orderedSlope hS hN j
    rwa [he, hat i] at hm
  refine ⟨n, U, b, hU, hz, ht, hrange, hb, hcut, hat, hright, hrec, hblock, hmin, ?_⟩
  intro f
  have hs := Submodule.sum_eq_sum_flag_rank_blocks U hU.monotone hz ht
    (fun j ↦ f (V.generalHNOrderedSlope hS hN j)) (fun i ↦ f (b i))
    (fun i j hlo hhi ↦ congrArg f (hblock i j hlo hhi))
  simpa only [ArakelovGeometry.finrank_flagQuotient_eq_sub U hU.monotone] using hs

end

end ArakelovGeometry.AdelicVectorBundle

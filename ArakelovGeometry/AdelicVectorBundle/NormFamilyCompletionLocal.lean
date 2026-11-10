/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Comparison
public import ArakelovGeometry.Analysis.NormFamilyMetricLocalLimit

/-!
# Actual completed-fibre limits of norm families

Local Cauchy sequences for the source logarithmic distance have genuine
completed-fibre norm limits. Choosing these at every place gives an actual
norm family and convergence in every local distance, without measurability
or domination assumptions.
-/

@[expose] public section

open Filter
open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- A local-distance Cauchy sequence has an actual separating seminorm limit
on the literal completed scalar extension. -/
theorem exists_fibreNorm_limit (ξ : ℕ → NormFamily S E) (ω : S.Ω)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      (ξ m).localDist (ξ n) ω < ε) :
    ∃ q : Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E),
      (∀ x, q x = 0 ↔ x = 0) ∧
      (∀ x, Tendsto (fun n ↦ (ξ n).norm ω x) atTop (nhds (q x))) ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x,
        |Real.log ((ξ n).norm ω x) - Real.log (q x)| ≤ ε := by
  apply exists_seminorm_limit_of_uniform_log_cauchy
    (fun n ↦ (ξ n).norm ω) (fun n ↦ (ξ n).norm_eq_zero_iff ω)
  intro ε hε
  obtain ⟨N, hN⟩ := hc ε hε
  exact ⟨N, fun m hm n hn x ↦
    ((ξ m).log_norm_sub_le_localDist (ξ n) ω x).trans_lt (hN m hm n hn)⟩

/-- Almost-everywhere local Cauchy behavior produces an actual norm family,
with a single conull set on which the entire fibre distances converge to zero. -/
theorem exists_limit_of_ae_localDist_cauchy (ξ : ℕ → NormFamily S E)
    (hc : ∀ᵐ ω ∂S.v, ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      (ξ m).localDist (ξ n) ω < ε) :
    ∃ η : NormFamily S E, ∀ᵐ ω ∂S.v,
      Tendsto (fun n ↦ (ξ n).localDist η ω) atTop (nhds 0) := by
  classical
  let P : S.Ω → Prop := fun ω ↦ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
    (ξ m).localDist (ξ n) ω < ε
  have hex (ω : S.Ω) :
      ∃ q : Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E),
        (∀ x, q x = 0 ↔ x = 0) ∧
        (P ω → ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x,
          |Real.log ((ξ n).norm ω x) - Real.log (q x)| ≤ ε) := by
    by_cases hω : P ω
    · obtain ⟨q, hq, _, hlim⟩ := exists_fibreNorm_limit ξ ω hω
      exact ⟨q, hq, fun _ ↦ hlim⟩
    · exact ⟨(ξ 0).norm ω, (ξ 0).norm_eq_zero_iff ω, fun h ↦ (hω h).elim⟩
  choose q hq hlim using hex
  let η : NormFamily S E := ⟨q, hq⟩
  refine ⟨η, hc.mono fun ω hω ↦ ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hlim ω hω (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ((ξ n).localDist_nonneg η ω)]
  exact ((ξ n).localDist_le η ω (hN n hn)).trans_lt (half_lt_self hε)

/-- A uniform local-distance bound survives a local norm-family limit. -/
theorem localDist_le_of_tendsto (ξ : ℕ → NormFamily S E) (ζ η : NormFamily S E)
    (ω : S.Ω) {C : ℝ}
    (hlim : Tendsto (fun n ↦ (ξ n).localDist η ω) atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop, ζ.localDist (ξ n) ω ≤ C) :
    ζ.localDist η ω ≤ C := by
  have h : Tendsto (fun n ↦ C + (ξ n).localDist η ω) atTop (nhds C) := by
    simpa only [add_zero] using tendsto_const_nhds.add hlim
  apply ge_of_tendsto h
  exact hbound.mono fun n hn ↦
    (ζ.localDist_triangle (ξ n) η ω).trans (add_le_add hn le_rfl)

end ArakelovGeometry.NormFamily

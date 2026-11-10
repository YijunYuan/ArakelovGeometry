/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamilyCompletionLocal
public import ArakelovGeometry.AdelicVectorBundle.NormFamilyCompletionMetric
public import ArakelovGeometry.Analysis.NormFamilyMetricSummation

/-!
# Completeness of strongly dominated norm families

Summable integrable local-distance majorants produce an actual strongly
dominated limit family. This proves completeness of the upper-integral
pseudometric and its canonical quotient by almost-everywhere fibre equality,
as in Chen–Moriwaki, Remark 4.1.20.
-/

@[expose] public section

open MeasureTheory Filter

namespace ArakelovGeometry

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

@[instance_reducible]
private noncomputable def localNormFamilyPseudoMetric (ω : S.Ω) :
    PseudoMetricSpace (NormFamily S E) where
  dist ξ η := ξ.localDist η ω
  dist_self ξ := ξ.localDist_self ω
  dist_comm ξ η := ξ.localDist_comm η ω
  dist_triangle ξ η ζ := ξ.localDist_triangle η ζ ω

namespace StronglyDominatedNormFamily

variable [Fact (S.v S.Ωinf < ⊤)]

/-- Summable measurable majorants of consecutive local distances produce a
strongly dominated limit in the actual upper-integral pseudometric. -/
theorem exists_limit_of_summable_majorants (ξ : ℕ → StronglyDominatedNormFamily S E)
    (A : ℕ → S.Ω → ℝ) (hAm : ∀ n, Measurable (A n))
    (hAi : ∀ n, Integrable (A n) S.v) (hAp : ∀ n ω, 0 ≤ A n ω)
    (hAs : Summable fun n ↦ ∫ ω, A n ω ∂S.v)
    (hbound : ∀ n, ∀ᵐ ω ∂S.v, (ξ n).val.localDist (ξ (n + 1)).val ω ≤ A n ω) :
    ∃ η : StronglyDominatedNormFamily S E, Tendsto ξ atTop (nhds η) := by
  have hsum := (nonneg_summable_integral_majorants A hAm hAi hAp hAs).1
  have htail := nonneg_summable_integral_majorant_tails A hAm hAi hAp hAs
  have hc : ∀ᵐ ω ∂S.v, ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      (ξ m).val.localDist (ξ n).val ω < ε := by
    filter_upwards [hsum, ae_all_iff.mpr hbound] with ω hs hb
    let := localNormFamilyPseudoMetric (S := S) (E := E) ω
    have hdist : Summable fun n ↦ dist (ξ n).val (ξ (n + 1)).val :=
      Summable.of_nonneg_of_le (fun n ↦ (ξ n).val.localDist_nonneg _ ω) hb hs
    exact Metric.cauchySeq_iff.mp (cauchySeq_of_summable_dist hdist)
  obtain ⟨η, hηlim⟩ := NormFamily.exists_limit_of_ae_localDist_cauchy (fun n ↦ (ξ n).val) hc
  have hηbound (k : ℕ) : ∀ᵐ ω ∂S.v,
      (ξ k).val.localDist η ω ≤ ∑' n, A (n + k) ω := by
    filter_upwards [hsum, ae_all_iff.mpr hbound, hηlim] with ω hs hb hlim
    let := localNormFamilyPseudoMetric (S := S) (E := E) ω
    have ht : Tendsto (fun n ↦ (ξ n).val) atTop (nhds η) :=
      tendsto_iff_dist_tendsto_zero.mpr hlim
    have h := dist_le_tsum_of_dist_le_of_tendsto (fun n ↦ A n ω) hb hs ht k
    change (ξ k).val.localDist η ω ≤ ∑' n, A (k + n) ω at h
    simpa only [Nat.add_comm] using h
  have hηdom : η.IsStronglyDominated := (ξ 0).property.of_localDist
    ⟨fun ω ↦ ∑' n, A (n + 0) ω, htail.1 0, hηbound 0⟩
  let η' : StronglyDominatedNormFamily S E := ⟨η, hηdom⟩
  refine ⟨η', tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ htail.2.2
  intro k
  have hi : (ξ k).val.upperIntegralDist η ≤ (∫ ω, ∑' n, A (n + k) ω ∂S.v : ℝ) :=
    sInf_le ⟨fun ω ↦ ∑' n, A (n + k) ω, htail.1 k, hηbound k, rfl⟩
  rw [← dist_eq_upperIntegralDist (ξ k) η'] at hi
  exact EReal.coe_le_coe_iff.mp hi

/-- Strongly dominated norm families form a complete pseudometric space. -/
noncomputable instance instCompleteSpace : CompleteSpace (StronglyDominatedNormFamily S E) := by
  apply Metric.complete_of_convergent_controlled_sequences (fun n ↦ (1 / 2 : ℝ) ^ n)
    (fun n ↦ pow_pos (by norm_num) n)
  intro ξ hξ
  have hex (n : ℕ) : ∃ A : S.Ω → ℝ, Measurable A ∧ Integrable A S.v ∧
      (∀ ω, 0 ≤ A ω) ∧ (ξ n).val.localDist (ξ (n + 1)).val ≤ᵐ[S.v] A ∧
      ∫ ω, A ω ∂S.v < 2 * (1 / 2 : ℝ) ^ n := by
    apply exists_nonneg_measurable_upper_envelope_lt
      (Eventually.of_forall ((ξ n).val.localDist_nonneg _))
    change (ξ n).val.upperIntegralDist (ξ (n + 1)).val < _
    rw [← dist_eq_upperIntegralDist]
    apply EReal.coe_lt_coe_iff.mpr
    have h := hξ n n (n + 1) le_rfl (Nat.le_succ n)
    have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
    linarith
  choose A hAm hAi hAp hbound hAlt using hex
  apply exists_limit_of_summable_majorants ξ A hAm hAi hAp _ hbound
  exact Summable.of_nonneg_of_le (fun n ↦ integral_nonneg (hAp n))
    (fun n ↦ (hAlt n).le)
    ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left 2)

/-- The canonical metric quotient by almost-everywhere equality is complete. -/
theorem completeSpace_aeQuotient : CompleteSpace (AEQuotient S E) := inferInstance

end StronglyDominatedNormFamily

end ArakelovGeometry

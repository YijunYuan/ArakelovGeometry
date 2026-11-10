/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Limits of uniformly logarithmically Cauchy norms

The local completeness producer in Chen–Moriwaki, Remark 4.1.20.
Uniformly Cauchy logarithmic evaluations produce an actual separating
seminorm, with both pointwise norm convergence and uniform logarithmic
convergence. The argument works over any normed field, including trivial
valuations, and does not require finite dimensionality.
-/

open Filter

namespace ArakelovGeometry

/-- A sequence of actual norms which is uniformly Cauchy after logarithms
converges to an actual norm, uniformly in logarithmic discrepancy. -/
theorem exists_seminorm_limit_of_uniform_log_cauchy
    {𝕜 V : Type*} [NormedField 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (p : ℕ → Seminorm 𝕜 V) (hp : ∀ n x, p n x = 0 ↔ x = 0)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x : V,
      |Real.log (p m x) - Real.log (p n x)| < ε) :
    ∃ q : Seminorm 𝕜 V, (∀ x, q x = 0 ↔ x = 0) ∧
      (∀ x, Tendsto (fun n ↦ p n x) atTop (nhds (q x))) ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : V,
        |Real.log (p n x) - Real.log (q x)| ≤ ε := by
  classical
  have hp_pos (n : ℕ) (x : V) (hx : x ≠ 0) : 0 < p n x :=
    lt_of_le_of_ne' (apply_nonneg _ _) (fun h ↦ hx ((hp n x).mp h))
  have hlog (x : V) : CauchySeq (fun n ↦ Real.log (p n x)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    exact ⟨N, fun m hm n hn ↦ by simpa only [Real.dist_eq] using hN m hm n hn x⟩
  choose r hr using fun x ↦ cauchySeq_tendsto_of_complete (hlog x)
  let qf : V → ℝ := fun x ↦ if x = 0 then 0 else Real.exp (r x)
  have hqt (x : V) : Tendsto (fun n ↦ p n x) atTop (nhds (qf x)) := by
    by_cases hx : x = 0
    · subst x
      simpa only [map_zero, qf, if_pos rfl] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
    · have h := (Real.continuous_exp.tendsto (r x)).comp (hr x)
      simpa only [Function.comp_def, qf, if_neg hx, Real.exp_log (hp_pos _ x hx)] using h
  have hqzero : qf 0 = 0 := by simp [qf]
  let q : Seminorm 𝕜 V :=
    { toFun := qf
      map_zero' := hqzero
      add_le' := fun x y ↦ le_of_tendsto_of_tendsto (hqt (x + y))
        ((hqt x).add (hqt y)) (Eventually.of_forall fun n ↦ map_add_le_add (p n) x y)
      neg' := fun x ↦ tendsto_nhds_unique (hqt (-x))
        (by simpa only [map_neg_eq_map] using hqt x)
      smul' := fun a x ↦ tendsto_nhds_unique (hqt (a • x))
        (by simpa only [map_smul_eq_mul] using (hqt x).const_mul ‖a‖) }
  have hqsep (x : V) : q x = 0 ↔ x = 0 := by
    change qf x = 0 ↔ x = 0
    by_cases hx : x = 0
    · simp [hx, hqzero]
    · simp [qf, hx, (Real.exp_pos (r x)).ne']
  refine ⟨q, hqsep, hqt, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := hc ε hε
  refine ⟨N, fun n hn x ↦ ?_⟩
  by_cases hx : x = 0
  · simp only [hx, map_zero, sub_self, abs_zero]
    exact hε.le
  · have hqne : q x ≠ 0 := fun h ↦ hx ((hqsep x).mp h)
    have ht := ((tendsto_const_nhds (x := Real.log (p n x))).sub
      ((hqt x).log hqne)).abs
    apply le_of_tendsto ht
    exact (eventually_ge_atTop N).mono fun m hm ↦ (hN n hn m hm x).le

end ArakelovGeometry

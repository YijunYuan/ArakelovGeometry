/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass
/-!
# Bounded functional monotone classes

Uniformly bounded pointwise limits, together with a bounded multiplicative
generating family, determine every bounded measurable real function.
This is the bounded monotone-class argument used in Chen–Moriwaki, Theorem 3.3.4.
-/

@[expose] public section
open Filter Topology
namespace MeasureTheory
variable {X : Type*}
private def boundedSeqClosed (S : Set (X → ℝ)) : Prop :=
  ∀ ⦃u : ℕ → X → ℝ⦄ ⦃f : X → ℝ⦄, (∀ n, u n ∈ S) →
    (∃ M : ℝ, ∀ n x, |u n x| ≤ M) → Tendsto u atTop (nhds f) → f ∈ S

private def boundedSequentialSpan (C : Set (X → ℝ)) : Submodule ℝ (X → ℝ) :=
  sInf {S | C ⊆ S ∧ boundedSeqClosed (S : Set (X → ℝ))}

private theorem subset_boundedSequentialSpan (C : Set (X → ℝ)) : C ⊆ boundedSequentialSpan C := by
  intro f hf
  exact Submodule.mem_sInf.mpr fun S hS ↦ hS.1 hf

private theorem boundedSequentialSpan_le {C : Set (X → ℝ)} {S : Submodule ℝ (X → ℝ)}
    (hC : C ⊆ S) (hS : boundedSeqClosed (S : Set (X → ℝ))) :
    boundedSequentialSpan C ≤ S := sInf_le ⟨hC, hS⟩

private theorem boundedSeqClosed_boundedSequentialSpan (C : Set (X → ℝ)) :
    boundedSeqClosed (boundedSequentialSpan C : Set (X → ℝ)) := by
  intro u f hu hbound hf
  apply Submodule.mem_sInf.mpr
  intro S hS
  exact hS.2 (fun n ↦ Submodule.mem_sInf.mp (hu n) S hS) hbound hf

private theorem boundedSequentialSpan_bounded {C : Set (X → ℝ)}
    (hC : ∀ f ∈ C, ∃ M : ℝ, ∀ x, |f x| ≤ M)
    {f : X → ℝ} (hf : f ∈ boundedSequentialSpan C) :
    ∃ M : ℝ, ∀ x, |f x| ≤ M := by
  let B : Submodule ℝ (X → ℝ) := {
    carrier := {f | ∃ M : ℝ, ∀ x, |f x| ≤ M}
    zero_mem' := ⟨0, by simp⟩
    add_mem' := by
      rintro f g ⟨M, hM⟩ ⟨N, hN⟩
      exact ⟨M + N, fun x ↦ (abs_add_le _ _).trans (add_le_add (hM x) (hN x))⟩
    smul_mem' := by
      rintro a f ⟨M, hM⟩
      refine ⟨|a| * M, fun x ↦ ?_⟩
      simpa only [Pi.smul_apply, smul_eq_mul, abs_mul] using
        mul_le_mul_of_nonneg_left (hM x) (abs_nonneg a) }
  have hB : boundedSeqClosed (B : Set (X → ℝ)) := by
    intro u g hu hbound hug
    obtain ⟨M, hM⟩ := hbound
    exact ⟨M, fun x ↦ le_of_tendsto (tendsto_pi_nhds.mp hug x).abs
      (Eventually.of_forall fun n ↦ hM n x)⟩
  exact boundedSequentialSpan_le (S := B) (fun g hg ↦ hC g hg) hB hf

private theorem uniformBound_mul_right {u : ℕ → X → ℝ} {g : X → ℝ}
    (hu : ∃ M : ℝ, ∀ n x, |u n x| ≤ M) (hg : ∃ N : ℝ, ∀ x, |g x| ≤ N) :
    ∃ R : ℝ, ∀ n x, |(u n * g) x| ≤ R := by
  obtain ⟨M, hM⟩ := hu
  obtain ⟨N, hN⟩ := hg
  refine ⟨|M| * |N|, fun n x ↦ ?_⟩
  exact (abs_mul _ _).le.trans (mul_le_mul ((hM n x).trans (le_abs_self M))
    ((hN x).trans (le_abs_self N)) (abs_nonneg _) (abs_nonneg _))

private theorem boundedSequentialSpan_mul {C : Set (X → ℝ)}
    (hCb : ∀ f ∈ C, ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    {f g : X → ℝ} (hf : f ∈ boundedSequentialSpan C) (hg : g ∈ boundedSequentialSpan C) :
    f * g ∈ boundedSequentialSpan C := by
  let D := boundedSequentialSpan C
  have hD := boundedSeqClosed_boundedSequentialSpan C
  have hright (g : X → ℝ) (hg : g ∈ C) : ∀ f ∈ D, f * g ∈ D := by
    have hle : D ≤ D ⊓ D.comap (LinearMap.mulRight ℝ g) := by
      apply boundedSequentialSpan_le
      · intro f hf
        exact ⟨subset_boundedSequentialSpan C hf, subset_boundedSequentialSpan C (hC f hf g hg)⟩
      · intro u f hu hub huf
        exact ⟨hD (fun n ↦ (hu n).1) hub huf,
          hD (fun n ↦ (hu n).2) (uniformBound_mul_right hub (hCb g hg)) (huf.mul_const g)⟩
    exact fun f hf ↦ (hle hf).2
  have hle : D ≤ D ⊓ D.comap (LinearMap.mulLeft ℝ f) := by
    apply boundedSequentialSpan_le
    · intro g hg
      exact ⟨subset_boundedSequentialSpan C hg, hright g hg f hf⟩
    · intro u g hu hub hug
      have hb : ∃ M : ℝ, ∀ n x, |(f * u n) x| ≤ M := by
        simpa only [mul_comm] using
          uniformBound_mul_right hub (boundedSequentialSpan_bounded hCb hf)
      exact ⟨hD (fun n ↦ (hu n).1) hub hug,
        hD (fun n ↦ (hu n).2) hb (hug.const_mul f)⟩
  exact (hle hg).2

private theorem boundedSequentialSpan_const {C : Set (X → ℝ)} (h1 : (1 : X → ℝ) ∈ C) (a : ℝ) :
    (fun _ : X ↦ a) ∈ boundedSequentialSpan C := by
  simpa only [Pi.smul_def, Pi.one_apply, smul_eq_mul, mul_one] using
    (boundedSequentialSpan C).smul_mem a (subset_boundedSequentialSpan C h1)

private theorem boundedSequentialSpan_polynomial {C : Set (X → ℝ)}
    (hCb : ∀ f ∈ C, ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    {f : X → ℝ} (hf : f ∈ boundedSequentialSpan C) (p : Polynomial ℝ) :
    (fun x ↦ p.eval (f x)) ∈ boundedSequentialSpan C := by
  induction p using Polynomial.induction_on with
  | C a => simpa using boundedSequentialSpan_const h1 a
  | add p q hp hq =>
      simpa only [Polynomial.eval_add, Pi.add_def] using (boundedSequentialSpan C).add_mem hp hq
  | monomial n a hn =>
      simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, pow_succ, mul_assoc, Pi.mul_def] using
          boundedSequentialSpan_mul hCb hC hn hf

private theorem boundedSequentialSpan_abs {C : Set (X → ℝ)}
    (hCb : ∀ f ∈ C, ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    {f : X → ℝ} (hf : f ∈ boundedSequentialSpan C) :
    (fun x ↦ |f x|) ∈ boundedSequentialSpan C := by
  obtain ⟨M, hM⟩ := boundedSequentialSpan_bounded hCb hf
  choose p hp using fun n : ℕ ↦
    exists_polynomial_near_of_continuousOn (-|M|) |M| (fun t : ℝ ↦ |t|)
      continuous_abs.continuousOn (1 / (n + 1)) (by positivity)
  have he (n : ℕ) (x : X) :
      dist ((p n).eval (f x)) |f x| < 1 / (n + 1) :=
    hp n (f x) (abs_le.mp ((hM x).trans (le_abs_self M)))
  apply boundedSeqClosed_boundedSequentialSpan C
    (fun n ↦ boundedSequentialSpan_polynomial hCb h1 hC hf (p n))
  · refine ⟨|M|+1, fun n x ↦ ?_⟩
    have he' := he n x
    rw [Real.dist_eq] at he'
    have he1 := (abs_le.mp he'.le).1
    have he2 := (abs_le.mp he'.le).2
    have hn : 1 / ((n : ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hx := (hM x).trans (le_abs_self M)
    apply abs_le.mpr
    constructor <;> nlinarith [abs_nonneg (f x), abs_nonneg M]
  · apply tendsto_pi_nhds.mpr
    intro x
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (he n x).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
private theorem boundedSequentialSpan_min {C : Set (X → ℝ)}
    (hCb : ∀ f ∈ C, ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    {f g : X → ℝ} (hf : f ∈ boundedSequentialSpan C) (hg : g ∈ boundedSequentialSpan C) :
    (fun x ↦ min (f x) (g x)) ∈ boundedSequentialSpan C := by
  have ha := boundedSequentialSpan_abs hCb h1 hC ((boundedSequentialSpan C).sub_mem hf hg)
  convert (boundedSequentialSpan C).smul_mem (1 / 2 : ℝ)
    ((boundedSequentialSpan C).sub_mem ((boundedSequentialSpan C).add_mem hf hg) ha) using 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply]
  rw [min_def]
  split_ifs with hx
  · rw [abs_of_nonpos (sub_nonpos.mpr hx)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (not_le.mp hx).le)]
    ring

private theorem boundedSequentialSpan_max {C : Set (X → ℝ)}
    (hCb : ∀ f ∈ C, ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    {f g : X → ℝ} (hf : f ∈ boundedSequentialSpan C) (hg : g ∈ boundedSequentialSpan C) :
    (fun x ↦ max (f x) (g x)) ∈ boundedSequentialSpan C := by
  convert (boundedSequentialSpan C).sub_mem ((boundedSequentialSpan C).add_mem hf hg)
    (boundedSequentialSpan_min hCb h1 hC hf hg) using 1
  funext x
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [min_def, max_def]
  split_ifs <;> ring

private theorem boundedSequentialSpan_indicator_gt {C : Set (X → ℝ)}
    (hCb : ∀ f ∈ C, ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    {f : X → ℝ} (hf : f ∈ boundedSequentialSpan C) (r : ℝ) :
    {x | r < f x}.indicator (fun _ ↦ (1 : ℝ)) ∈ boundedSequentialSpan C := by
  classical
  refine boundedSeqClosed_boundedSequentialSpan C
    (u := fun n : ℕ ↦ fun x ↦ min 1 ((n : ℝ) * max 0 (f x - r))) ?_ ?_ ?_
  · intro n
    exact boundedSequentialSpan_min hCb h1 hC (boundedSequentialSpan_const h1 1)
      ((boundedSequentialSpan C).smul_mem (n : ℝ)
        (boundedSequentialSpan_max hCb h1 hC (boundedSequentialSpan_const h1 0)
          ((boundedSequentialSpan C).sub_mem hf (boundedSequentialSpan_const h1 r))))
  · refine ⟨1, fun n x ↦ ?_⟩
    rw [abs_of_nonneg (le_min zero_le_one (by positivity))]
    exact min_le_left _ _
  · apply tendsto_pi_nhds.mpr
    intro x
    by_cases hx : r < f x
    · apply tendsto_const_nhds.congr'
      filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
        (1 / (f x - r))] with n hn
      simp only [Set.indicator, Set.mem_ofPred_eq, hx, ↓reduceIte,
        max_eq_right (le_of_lt (sub_pos.mpr hx)),
        min_eq_left ((div_le_iff₀ (sub_pos.mpr hx)).mp hn)]
    · simp [max_eq_left (sub_nonpos.mpr (not_lt.mp hx)), hx]

private abbrev boundedSequentialSpanMeasurableSpace {C : Set (X → ℝ)}
    (hCb : ∀ f ∈ C, ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C) :
    MeasurableSpace X := by
  classical
  refine {
    MeasurableSet' := fun s ↦ s.indicator (fun _ ↦ (1 : ℝ)) ∈ boundedSequentialSpan C
    measurableSet_empty := by
      rw [Set.indicator_empty]
      exact (boundedSequentialSpan C).zero_mem
    measurableSet_compl := fun s hs ↦ ?_
    measurableSet_iUnion := fun s hs ↦ ?_ }
  · rw [Set.indicator_compl]
    exact (boundedSequentialSpan C).sub_mem (boundedSequentialSpan_const h1 1) hs
  · refine boundedSeqClosed_boundedSequentialSpan C
      (u := fun n : ℕ ↦ fun x ↦ min 1
        (∑ i ∈ Finset.range n, (s i).indicator (fun _ ↦ (1 : ℝ)) x)) ?_ ?_ ?_
    · intro n
      change (fun x ↦ min (1 : ℝ) (∑ i ∈ Finset.range n,
        (s i).indicator (fun _ ↦ (1 : ℝ)) x)) ∈ boundedSequentialSpan C
      have hsum : (∑ i ∈ Finset.range n, (s i).indicator (fun _ ↦ (1 : ℝ))) ∈
          boundedSequentialSpan C := (boundedSequentialSpan C).sum_mem fun i _ ↦ hs i
      simpa only [Finset.sum_apply] using
        boundedSequentialSpan_min hCb h1 hC (boundedSequentialSpan_const h1 1) hsum
    · refine ⟨1, fun n x ↦ ?_⟩
      rw [abs_of_nonneg (le_min zero_le_one (Finset.sum_nonneg
        fun i _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x))]
      exact min_le_left _ _
    · apply tendsto_pi_nhds.mpr
      intro x
      by_cases hx : x ∈ ⋃ i, s i
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop (i + 1)] with n hn
        have hsum : (1 : ℝ) ≤ ∑ j ∈ Finset.range n,
            (s j).indicator (fun _ ↦ (1 : ℝ)) x := by
          calc
            1 = (s i).indicator (fun _ ↦ (1 : ℝ)) x := by simp [hi]
            _ ≤ _ := Finset.single_le_sum
              (fun j _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x)
              (Finset.mem_range.mpr (by omega))
        simp only [Set.indicator_of_mem hx, min_eq_left hsum]
      · have hx' : ∀ i, x ∉ s i := fun i hi ↦ hx (Set.mem_iUnion.mpr ⟨i, hi⟩)
        simp [hx, hx']

/-- A vector space closed under uniformly bounded pointwise sequential limits and containing
a bounded multiplicative family contains every bounded function measurable for that family. -/
theorem measurable_mem_of_bounded_pointwise_closed {C : Set (X → ℝ)}
    (H : Submodule ℝ (X → ℝ))
    (hH : ∀ ⦃u : ℕ → X → ℝ⦄ ⦃f : X → ℝ⦄, (∀ n, u n ∈ H) →
      (∃ M : ℝ, ∀ n x, |u n x| ≤ M) → Tendsto u atTop (nhds f) → f ∈ H)
    (hCb : ∀ f ∈ C, ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    (hCH : C ⊆ H) {f : X → ℝ}
    (hf : @Measurable X ℝ (⨆ g : C, MeasurableSpace.comap g.val inferInstance) _ f)
    (hfb : ∃ M : ℝ, ∀ x, |f x| ≤ M) : f ∈ H := by
  let m := boundedSequentialSpanMeasurableSpace hCb h1 hC
  have hm : (⨆ g : C, MeasurableSpace.comap g.val inferInstance) ≤ m := by
    apply iSup_le
    intro g
    apply measurable_iff_comap_le.mp
    apply measurable_of_Ioi
    intro r
    exact boundedSequentialSpan_indicator_gt hCb h1 hC (subset_boundedSequentialSpan C g.property) r
  have hfm : @Measurable X ℝ m _ f := hf.mono hm le_rfl
  let := m
  obtain ⟨s, hs⟩ := hfm.stronglyMeasurable
  obtain ⟨M, hM⟩ := hfb
  let t (n : ℕ) : SimpleFunc X ℝ :=
    (s n).map (fun r ↦ max (-|M|) (min |M| r))
  have ht (n : ℕ) : (t n : X → ℝ) ∈ boundedSequentialSpan C := by
    induction t n using SimpleFunc.induction with
    | @const a S hS =>
        have hi : S.indicator (fun _ ↦ (1 : ℝ)) ∈ boundedSequentialSpan C := hS
        change S.indicator (fun _ ↦ a) ∈ boundedSequentialSpan C
        have heq : S.indicator (fun _ ↦ a) = a • S.indicator (fun _ ↦ (1 : ℝ)) := by
          ext x
          by_cases hx : x ∈ S <;> simp [hx, smul_eq_mul]
        rw [heq]
        exact (boundedSequentialSpan C).smul_mem a hi
    | add huv hu hv =>
        exact (boundedSequentialSpan C).add_mem hu hv
  apply boundedSequentialSpan_le hCH hH
  apply boundedSeqClosed_boundedSequentialSpan C ht
  · refine ⟨|M|, fun n x ↦ ?_⟩
    change |max (-|M|) (min |M| (s n x))| ≤ |M|
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith [abs_nonneg M]) (min_le_left _ _)⟩
  · apply tendsto_pi_nhds.mpr
    intro x
    have hx : f x ∈ Set.Icc (-|M|) |M| := abs_le.mp ((hM x).trans (le_abs_self M))
    have hc : Continuous (fun r : ℝ ↦ max (-|M|) (min |M| r)) :=
      continuous_const.max (continuous_const.min continuous_id)
    have htend := hc.continuousAt.tendsto.comp (hs x)
    change Tendsto (fun n ↦ max (-|M|) (min |M| (s n x))) atTop (nhds (f x))
    simpa only [Function.comp_def, min_eq_right hx.2, max_eq_right hx.1] using htend

end MeasureTheory

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Functional monotone classes under pointwise sequential limits

A real vector space of functions that contains a multiplicative generating family and
is closed under pointwise sequential limits contains all functions measurable for the
generated sigma algebra. The proof constructs the minimal such vector space, proves
that it is an algebra, and obtains indicators by polynomial approximation and limits.
-/

open Filter Topology
namespace MeasureTheory
variable {X : Type*}
private def sequentialSpan (C : Set (X → ℝ)) : Submodule ℝ (X → ℝ) :=
  sInf {S | C ⊆ S ∧ IsSeqClosed (S : Set (X → ℝ))}

private theorem subset_sequentialSpan (C : Set (X → ℝ)) :
    C ⊆ sequentialSpan C := by
  intro f hf
  exact Submodule.mem_sInf.mpr fun S hS ↦ hS.1 hf

private theorem sequentialSpan_le {C : Set (X → ℝ)} {S : Submodule ℝ (X → ℝ)}
    (hC : C ⊆ S) (hS : IsSeqClosed (S : Set (X → ℝ))) :
    sequentialSpan C ≤ S := sInf_le ⟨hC, hS⟩

private theorem isSeqClosed_sequentialSpan (C : Set (X → ℝ)) :
    IsSeqClosed (sequentialSpan C : Set (X → ℝ)) := by
  intro u f hu hf
  apply Submodule.mem_sInf.mpr
  intro S hS
  exact hS.2 (fun n ↦ Submodule.mem_sInf.mp (hu n) S hS) hf

private theorem sequentialSpan_mul {C : Set (X → ℝ)}
    (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    {f g : X → ℝ} (hf : f ∈ sequentialSpan C) (hg : g ∈ sequentialSpan C) :
    f * g ∈ sequentialSpan C := by
  let D := sequentialSpan C
  have hD := isSeqClosed_sequentialSpan C
  have hright (g : X → ℝ) (hg : g ∈ C) : ∀ f ∈ D, f * g ∈ D := by
    have hle : D ≤ D ⊓ D.comap (LinearMap.mulRight ℝ g) := by
      apply sequentialSpan_le
      · intro f hf
        exact ⟨subset_sequentialSpan C hf, subset_sequentialSpan C (hC f hf g hg)⟩
      · intro u f hu huf
        exact ⟨hD (fun n ↦ (hu n).1) huf,
          hD (fun n ↦ (hu n).2) (huf.mul_const g)⟩
    intro f hf
    exact (hle hf).2
  have hle : D ≤ D ⊓ D.comap (LinearMap.mulLeft ℝ f) := by
    apply sequentialSpan_le
    · intro g hg
      exact ⟨subset_sequentialSpan C hg, hright g hg f hf⟩
    · intro u g hu hug
      exact ⟨hD (fun n ↦ (hu n).1) hug,
        hD (fun n ↦ (hu n).2) (hug.const_mul f)⟩
  exact (hle hg).2

private theorem sequentialSpan_const {C : Set (X → ℝ)} (h1 : (1 : X → ℝ) ∈ C)
    (a : ℝ) : (fun _ : X ↦ a) ∈ sequentialSpan C := by
  simpa only [Pi.smul_def, Pi.one_apply, smul_eq_mul, mul_one] using
    (sequentialSpan C).smul_mem a (subset_sequentialSpan C h1)

private theorem sequentialSpan_polynomial {C : Set (X → ℝ)}
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    {f : X → ℝ} (hf : f ∈ sequentialSpan C) (p : Polynomial ℝ) :
    (fun x ↦ p.eval (f x)) ∈ sequentialSpan C := by
  induction p using Polynomial.induction_on with
  | C a => simpa using sequentialSpan_const h1 a
  | add p q hp hq =>
      simpa only [Polynomial.eval_add, Pi.add_def] using (sequentialSpan C).add_mem hp hq
  | monomial n a hn =>
      simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, pow_succ, mul_assoc, Pi.mul_def] using
        sequentialSpan_mul hC hn hf

private theorem sequentialSpan_continuous_comp {C : Set (X → ℝ)}
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    {f : X → ℝ} (hf : f ∈ sequentialSpan C)
    {u : ℝ → ℝ} (hu : Continuous u) :
    u ∘ f ∈ sequentialSpan C := by
  choose p hp using fun n : ℕ ↦
    exists_polynomial_near_of_continuousOn (-(n : ℝ)) n u hu.continuousOn
      (1 / (n + 1)) (by positivity)
  apply isSeqClosed_sequentialSpan C (fun n ↦ sequentialSpan_polynomial h1 hC hf (p n))
  apply tendsto_pi_nhds.mpr
  intro x
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop |f x|] with n hn
  exact (hp n (f x) (abs_le.mp hn)).le


private theorem sequentialSpan_indicator_gt {C : Set (X → ℝ)}
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    {f : X → ℝ} (hf : f ∈ sequentialSpan C) (r : ℝ) :
    {x | r < f x}.indicator (fun _ ↦ (1 : ℝ)) ∈ sequentialSpan C := by
  classical
  refine isSeqClosed_sequentialSpan C
    (x := fun n : ℕ ↦ fun x ↦ min 1 ((n : ℝ) * max 0 (f x - r))) ?_ ?_
  · intro n
    exact sequentialSpan_continuous_comp h1 hC hf
      (continuous_const.min (continuous_const.mul
        (continuous_const.max (continuous_id.sub continuous_const))))
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

private abbrev sequentialSpanMeasurableSpace {C : Set (X → ℝ)}
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C) :
    MeasurableSpace X := by
  classical
  refine {
    MeasurableSet' := fun s ↦ s.indicator (fun _ ↦ (1 : ℝ)) ∈ sequentialSpan C
    measurableSet_empty := by
      rw [Set.indicator_empty]
      exact (sequentialSpan C).zero_mem
    measurableSet_compl := fun s hs ↦ ?_
    measurableSet_iUnion := fun s hs ↦ ?_ }
  · rw [Set.indicator_compl]
    exact (sequentialSpan C).sub_mem (sequentialSpan_const h1 1) hs
  · refine isSeqClosed_sequentialSpan C
      (x := fun n : ℕ ↦ fun x ↦ min 1
        (∑ i ∈ Finset.range n, (s i).indicator (fun _ ↦ (1 : ℝ)) x)) ?_ ?_
    · intro n
      change (fun x ↦ min (1 : ℝ) (∑ i ∈ Finset.range n,
        (s i).indicator (fun _ ↦ (1 : ℝ)) x)) ∈ sequentialSpan C
      have hsum : (∑ i ∈ Finset.range n, (s i).indicator (fun _ ↦ (1 : ℝ))) ∈
          sequentialSpan C := (sequentialSpan C).sum_mem fun i _ ↦ hs i
      simpa only [Function.comp_def, Finset.sum_apply, id_eq] using
        sequentialSpan_continuous_comp h1 hC hsum (continuous_const.min continuous_id)
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

/-- A sequentially closed real vector space containing a multiplicative family and one
contains every real function measurable for the sigma algebra generated by that family. -/
theorem measurable_mem_of_isSeqClosed {C : Set (X → ℝ)} (H : Submodule ℝ (X → ℝ))
    (hH : IsSeqClosed (H : Set (X → ℝ)))
    (h1 : (1 : X → ℝ) ∈ C) (hC : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C)
    (hCH : C ⊆ H) {f : X → ℝ}
    (hf : @Measurable X ℝ (⨆ g : C, MeasurableSpace.comap g.val inferInstance) _ f) :
    f ∈ H := by
  let m := sequentialSpanMeasurableSpace h1 hC
  have hm : (⨆ g : C, MeasurableSpace.comap g.val inferInstance) ≤ m := by
    apply iSup_le
    intro g
    apply measurable_iff_comap_le.mp
    apply measurable_of_Ioi
    intro r
    exact sequentialSpan_indicator_gt h1 hC (subset_sequentialSpan C g.property) r
  have hfm : @Measurable X ℝ m _ f := hf.mono hm le_rfl
  let := m
  obtain ⟨s, hs⟩ := hfm.stronglyMeasurable
  apply sequentialSpan_le hCH hH
  apply isSeqClosed_sequentialSpan C (x := fun n ↦ (s n : X → ℝ)) ?_ (tendsto_pi_nhds.mpr hs)
  intro n
  induction s n using SimpleFunc.induction with
  | @const a t ht =>
      have hi : t.indicator (fun _ ↦ (1 : ℝ)) ∈ sequentialSpan C := ht
      change (t.indicator (fun _ ↦ a)) ∈ sequentialSpan C
      have heq : t.indicator (fun _ ↦ a) = a • t.indicator (fun _ ↦ (1 : ℝ)) := by
        ext x
        by_cases hx : x ∈ t <;> simp [hx, smul_eq_mul]
      rw [heq]
      exact (sequentialSpan C).smul_mem a hi
  | add huv hu hv =>
      exact (sequentialSpan C).add_mem hu hv

end MeasureTheory

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Collapsing a probability summand

The measure-theoretic construction used in Chen–Moriwaki, Example 3.7.2(3).
On a disjoint union `A ⊕ B`, collapse a probability space `B` to one point.
The induced `L¹` operator fixes the `A` component and integrates over `B`.
-/

@[expose] public section

namespace ArakelovGeometry.ProbabilityCollapse

open MeasureTheory

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The disjoint-union measure, in the form used by adelic amalgamation. -/
noncomputable def sumMeasure (μ : Measure A) (ν : Measure B) : Measure (A ⊕ B) :=
  μ.map Sum.inl + ν.map Sum.inr

theorem embedding_inl : MeasurableEmbedding (@Sum.inl A B) :=
  ⟨Sum.inl_injective, measurable_inl, fun _ hs ↦ hs.inl_image⟩

theorem embedding_inr : MeasurableEmbedding (@Sum.inr A B) :=
  ⟨Sum.inr_injective, measurable_inr, fun _ hs ↦ hs.inr_image⟩

/-- Integrability on the sum is equivalent to integrability on both components. -/
theorem integrable_sumMeasure_iff (μ : Measure A) (ν : Measure B) {f : A ⊕ B → ℝ} :
    Integrable f (sumMeasure μ ν) ↔
      Integrable (f ∘ Sum.inl) μ ∧ Integrable (f ∘ Sum.inr) ν := by
  rw [sumMeasure, integrable_add_measure, embedding_inl.integrable_map_iff,
    embedding_inr.integrable_map_iff]

/-- Almost everywhere statements on a sum are componentwise. -/
theorem ae_sumMeasure_iff (μ : Measure A) (ν : Measure B) {p : A ⊕ B → Prop} :
    (∀ᵐ x ∂sumMeasure μ ν, p x) ↔
      (∀ᵐ a ∂μ, p (Sum.inl a)) ∧ (∀ᵐ b ∂ν, p (Sum.inr b)) := by
  rw [sumMeasure, ae_add_measure_iff, embedding_inl.ae_map_iff,
    embedding_inr.ae_map_iff]

/-- An integral on a disjoint union is the sum of the two component integrals. -/
theorem integral_sumMeasure (μ : Measure A) (ν : Measure B) {f : A ⊕ B → ℝ}
    (hf : Integrable f (sumMeasure μ ν)) :
    ∫ x, f x ∂sumMeasure μ ν =
      (∫ a, f (Sum.inl a) ∂μ) + ∫ b, f (Sum.inr b) ∂ν := by
  obtain ⟨h1, h2⟩ := integrable_add_measure.mp hf
  rw [sumMeasure, integral_add_measure h1 h2,
    embedding_inl.integral_map, embedding_inr.integral_map]

/-- Collapse the second component to a single point. -/
def collapse : A ⊕ B → A ⊕ Unit := Sum.elim Sum.inl (fun _ ↦ Sum.inr ())

theorem measurable_collapse : Measurable (collapse (A := A) (B := B)) :=
  measurable_fun_sum measurable_inl measurable_const

/-- Collapsing a probability component preserves the disjoint-union measures. -/
theorem measurePreserving_collapse (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure ν] :
    MeasurePreserving collapse (sumMeasure μ ν) (sumMeasure μ (Measure.dirac ())) := by
  refine ⟨measurable_collapse, ?_⟩
  rw [sumMeasure, Measure.map_add _ _ measurable_collapse,
    Measure.map_map measurable_collapse measurable_inl,
    Measure.map_map measurable_collapse measurable_inr]
  simp [collapse, Function.comp_def, sumMeasure, Measure.map_const,
    Measure.map_dirac' measurable_inr]

/-- Keep the first component and average the second component. -/
noncomputable def average (ν : Measure B) (f : A ⊕ B → ℝ) : A ⊕ Unit → ℝ :=
  Sum.elim (f ∘ Sum.inl) (fun _ ↦ ∫ b, f (Sum.inr b) ∂ν)

/-- Averaging sends integrable functions to integrable functions. -/
theorem integrable_average (μ : Measure A) (ν : Measure B) {f : A ⊕ B → ℝ}
    (hf : Integrable f (sumMeasure μ ν)) :
    Integrable (average ν f) (sumMeasure μ (Measure.dirac ())) := by
  apply (integrable_sumMeasure_iff _ _).mpr
  exact ⟨((integrable_sumMeasure_iff _ _).mp hf).1, integrable_const _⟩

/-- Averaging respects almost everywhere equality. -/
theorem average_congr_ae (μ : Measure A) (ν : Measure B) {f g : A ⊕ B → ℝ}
    (hfg : f =ᵐ[sumMeasure μ ν] g) :
    average ν f =ᵐ[sumMeasure μ (Measure.dirac ())] average ν g := by
  obtain ⟨h1, h2⟩ := (ae_sumMeasure_iff μ ν).mp hfg
  apply (ae_sumMeasure_iff _ _).mpr
  exact ⟨h1, Filter.Eventually.of_forall (fun _ ↦ integral_congr_ae h2)⟩

theorem average_add (μ : Measure A) (ν : Measure B) {f g : A ⊕ B → ℝ}
    (hf : Integrable f (sumMeasure μ ν)) (hg : Integrable g (sumMeasure μ ν)) :
    average ν (f + g) = average ν f + average ν g := by
  funext x
  cases x with
  | inl a => rfl
  | inr b =>
    exact integral_add ((integrable_sumMeasure_iff _ _).mp hf).2
      ((integrable_sumMeasure_iff _ _).mp hg).2

omit [MeasurableSpace A] in
theorem average_smul (ν : Measure B) (c : ℝ) (f : A ⊕ B → ℝ) :
    average ν (c • f) = c • average ν f := by
  funext x
  cases x with
  | inl a => rfl
  | inr b => exact integral_smul c _

/-- Averaging preserves the integral. -/
theorem integral_average (μ : Measure A) (ν : Measure B) {f : A ⊕ B → ℝ}
    (hf : Integrable f (sumMeasure μ ν)) :
    ∫ x, average ν f x ∂sumMeasure μ (Measure.dirac ()) =
      ∫ x, f x ∂sumMeasure μ ν := by
  rw [integral_sumMeasure _ _ (integrable_average μ ν hf), integral_sumMeasure _ _ hf]
  simp [average]

omit [MeasurableSpace A] in
/-- The average of a pullback along collapse recovers the original function. -/
theorem average_comp_collapse (ν : Measure B) [IsProbabilityMeasure ν]
    (g : A ⊕ Unit → ℝ) : average ν (g ∘ collapse) = g := by
  funext x
  cases x with
  | inl a => rfl
  | inr b => simp [average, collapse, Function.comp_def]

/-- The average as an integrable equivalence class. -/
noncomputable def averageL1 (μ : Measure A) (ν : Measure B)
    (f : Lp ℝ 1 (sumMeasure μ ν)) : Lp ℝ 1 (sumMeasure μ (Measure.dirac ())) :=
  (integrable_average μ ν (L1.integrable_coeFn f)).toL1 (average ν f)

theorem coeFn_averageL1 (μ : Measure A) (ν : Measure B)
    (f : Lp ℝ 1 (sumMeasure μ ν)) :
    averageL1 μ ν f =ᵐ[sumMeasure μ (Measure.dirac ())] average ν f :=
  Integrable.coeFn_toL1 _

theorem averageL1_add (μ : Measure A) (ν : Measure B)
    (f g : Lp ℝ 1 (sumMeasure μ ν)) :
    averageL1 μ ν (f + g) = averageL1 μ ν f + averageL1 μ ν g := by
  apply Lp.ext
  filter_upwards [coeFn_averageL1 μ ν (f + g),
    average_congr_ae μ ν (Lp.coeFn_add f g),
    coeFn_averageL1 μ ν f, coeFn_averageL1 μ ν g,
    Lp.coeFn_add (averageL1 μ ν f) (averageL1 μ ν g)] with x h1 h2 h3 h4 h5
  rw [average_add μ ν (L1.integrable_coeFn f) (L1.integrable_coeFn g)] at h2
  exact h1.trans (h2.trans ((congrArg₂ (· + ·) h3 h4).symm.trans h5.symm))

theorem averageL1_smul (μ : Measure A) (ν : Measure B)
    (c : ℝ) (f : Lp ℝ 1 (sumMeasure μ ν)) :
    averageL1 μ ν (c • f) = c • averageL1 μ ν f := by
  apply Lp.ext
  filter_upwards [coeFn_averageL1 μ ν (c • f),
    average_congr_ae μ ν (Lp.coeFn_smul c f),
    coeFn_averageL1 μ ν f, Lp.coeFn_smul c (averageL1 μ ν f)] with x h1 h2 h3 h4
  rw [average_smul] at h2
  exact h1.trans (h2.trans ((congrArg (c • ·) h3).symm.trans h4.symm))

/-- Averaging over a summand is a real-linear map on `L¹`. -/
noncomputable def averageL1LinearMap (μ : Measure A) (ν : Measure B) :
    Lp ℝ 1 (sumMeasure μ ν) →ₗ[ℝ] Lp ℝ 1 (sumMeasure μ (Measure.dirac ())) where
  toFun := averageL1 μ ν
  map_add' := averageL1_add μ ν
  map_smul' := averageL1_smul μ ν

/-- The operator has the stated representative on every integrable function. -/
theorem averageL1_toL1 (μ : Measure A) (ν : Measure B) {f : A ⊕ B → ℝ}
    (hf : Integrable f (sumMeasure μ ν)) :
    averageL1LinearMap μ ν (hf.toL1 f) =
      (integrable_average μ ν hf).toL1 (average ν f) := by
  apply Lp.ext
  exact (coeFn_averageL1 μ ν (hf.toL1 f)).trans
    ((average_congr_ae μ ν hf.coeFn_toL1).trans
      (integrable_average μ ν hf).coeFn_toL1.symm)

/-- The induced linear map preserves integrals. -/
theorem integral_averageL1 (μ : Measure A) (ν : Measure B)
    (f : Lp ℝ 1 (sumMeasure μ ν)) :
    ∫ x, averageL1LinearMap μ ν f x ∂sumMeasure μ (Measure.dirac ()) =
      ∫ x, f x ∂sumMeasure μ ν := by
  exact (integral_congr_ae (coeFn_averageL1 μ ν f)).trans
    (integral_average μ ν (L1.integrable_coeFn f))

/-- On `L¹`, averaging retracts pullback along the probability collapse. -/
theorem averageL1_compMeasurePreserving (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure ν] (g : Lp ℝ 1 (sumMeasure μ (Measure.dirac ()))) :
    averageL1LinearMap μ ν
      (Lp.compMeasurePreserving collapse (measurePreserving_collapse μ ν) g) = g := by
  apply Lp.ext
  exact (coeFn_averageL1 μ ν _).trans
    ((average_congr_ae μ ν
      (Lp.coeFn_compMeasurePreserving g (measurePreserving_collapse μ ν))).trans
      (Filter.Eventually.of_forall (congrFun (average_comp_collapse ν g))))

end ArakelovGeometry.ProbabilityCollapse

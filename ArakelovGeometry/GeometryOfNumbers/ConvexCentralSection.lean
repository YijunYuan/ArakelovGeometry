/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.ConvexVolume

/-! # Actual central sections of symmetric compact convex sets -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.ConvexCentralSection

open MeasureTheory Set
open scoped ENNReal Pointwise

variable {U W : Type*}

/-- The actual section of a subset of a product at the second coordinate. -/
def sectionAt (C : Set (U × W)) (w : W) : Set U := {u | (u, w) ∈ C}

@[simp] theorem mem_sectionAt {C : Set (U × W)} {w : W} {u : U} :
    u ∈ sectionAt C w ↔ (u, w) ∈ C := Iff.rfl

/-- Outside the actual projection the actual section is empty. -/
theorem sectionAt_eq_empty_of_not_mem_projection {C : Set (U × W)} {w : W}
    (hw : w ∉ Prod.snd '' C) : sectionAt C w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact hw ⟨(u, w), hu, rfl⟩

@[simp] theorem sectionAt_empty (w : W) : sectionAt (∅ : Set (U × W)) w = ∅ := rfl

/-- A section of an actual product over a point of the second factor is its first factor. -/
theorem sectionAt_prod_of_mem (A : Set U) {B : Set W} {w : W} (hw : w ∈ B) :
    sectionAt (A ×ˢ B) w = A := by
  ext u
  simp [sectionAt, hw]

/-- A zero-dimensional second factor has only the central section. -/
theorem sectionAt_eq_central_of_subsingleton [Zero W] [Subsingleton W]
    (C : Set (U × W)) (w : W) : sectionAt C w = sectionAt C 0 := by
  rw [Subsingleton.elim w 0]

section Geometry

variable [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedSpace ℝ U] [NormedSpace ℝ W] in
/-- Compactness of the original body gives compact actual sections. -/
theorem isCompact_sectionAt {C : Set (U × W)} (hC : IsCompact C) (w : W) :
    IsCompact (sectionAt C w) := by
  exact (Function.LeftInverse.isClosedEmbedding (f := Prod.fst) (g := fun u : U => (u, w))
    (fun _ => rfl) continuous_fst (continuous_id.prodMk continuous_const)).isCompact_preimage hC

/-- Each actual affine section of a convex body is convex. -/
theorem convex_sectionAt {C : Set (U × W)} (hC : Convex ℝ C) (w : W) :
    Convex ℝ (sectionAt C w) := by
  intro u hu v hv r s hr hs hrs
  have h := hC hu hv hr hs hrs
  change (r • u + s • v, w) ∈ C
  simpa only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hrs, one_smul] using h

omit [NormedSpace ℝ U] [NormedSpace ℝ W] in
/-- Actual opposite sections are negatives when the original body is symmetric. -/
theorem sectionAt_neg {C : Set (U × W)} (hC : ∀ z ∈ C, -z ∈ C) (w : W) :
    sectionAt C (-w) = -sectionAt C w := by
  ext u
  change (u, -w) ∈ C ↔ (-u, w) ∈ C
  constructor
  · intro hu
    simpa only [Prod.neg_mk, neg_neg] using hC (u, -w) hu
  · intro hu
    simpa only [Prod.neg_mk, neg_neg] using hC (-u, w) hu

/-- Convexity puts the actual half-sum of opposite sections in the central section. -/
theorem half_sections_subset_central {C : Set (U × W)} (hC : Convex ℝ C) (w : W) :
    (1 / 2 : ℝ) • sectionAt C w + (1 / 2 : ℝ) • sectionAt C (-w) ⊆
      sectionAt C 0 := by
  rintro _ ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
  have h := hC hu hv (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simpa only [mem_sectionAt, Prod.smul_mk, Prod.mk_add_mk, smul_neg, add_neg_cancel] using h

/-- The literal half-difference of a section is contained in the central section. -/
theorem half_difference_subset_central {C : Set (U × W)} (hC : Convex ℝ C)
    (hsymm : ∀ z ∈ C, -z ∈ C) (w : W) :
    (1 / 2 : ℝ) • (sectionAt C w + -sectionAt C w) ⊆ sectionAt C 0 := by
  rintro _ ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
  apply half_sections_subset_central hC w
  refine ⟨(1 / 2 : ℝ) • u, ⟨u, hu, rfl⟩, (1 / 2 : ℝ) • v, ⟨v, ?_, rfl⟩, ?_⟩
  · rw [sectionAt_neg hsymm]
    exact hv
  · exact (smul_add (1 / 2 : ℝ) u v).symm

end Geometry

section Measure

variable [NormedAddCommGroup U] [NormedAddCommGroup W]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]

/-- Tonelli computes the product measure of the original body using its actual sections. -/
theorem lintegral_sectionAt (μ : Measure U) (ν : Measure W) [SFinite μ] [SFinite ν]
    {C : Set (U × W)} (hC : IsCompact C) :
    ∫⁻ w, μ (sectionAt C w) ∂ν = (μ.prod ν) C :=
  (Measure.prod_apply_symm hC.isClosed.measurableSet).symm

end Measure

section Haar

variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The central section has maximal actual Haar volume, including zero-volume sections. -/
theorem measure_sectionAt_le_central (μ : Measure U) [μ.IsAddHaarMeasure]
    {C : Set (U × W)} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ z ∈ C, -z ∈ C) (w : W) :
    μ (sectionAt C w) ≤ μ (sectionAt C 0) := by
  exact (ConvexVolume.measure_le_half_difference μ (isCompact_sectionAt hcompact w)
    (convex_sectionAt hconvex w)).trans
      (measure_mono (half_difference_subset_central hconvex hsymm w))

/-- Tonelli bounds the volume of the original body by its actual central section and projection.
The second factor may carry any s-finite Borel measure; Haar measures are a special case. -/
theorem measure_prod_le_central_mul_projection
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    (μ : Measure U) [μ.IsAddHaarMeasure] (ν : Measure W) [SFinite ν]
    {C : Set (U × W)} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ z ∈ C, -z ∈ C) :
    (μ.prod ν) C ≤ μ (sectionAt C 0) * ν (Prod.snd '' C) := by
  classical
  have hP := hcompact.image continuous_snd
  rw [← lintegral_sectionAt μ ν hcompact]
  calc
    (∫⁻ w, μ (sectionAt C w) ∂ν) ≤
        ∫⁻ w, (Prod.snd '' C).indicator (fun _ => μ (sectionAt C 0)) w ∂ν := by
      apply lintegral_mono
      intro w
      by_cases hw : w ∈ Prod.snd '' C
      · rw [indicator_of_mem hw]
        exact measure_sectionAt_le_central μ hcompact hconvex hsymm w
      · simp [indicator_of_notMem hw, sectionAt_eq_empty_of_not_mem_projection hw]
    _ = μ (sectionAt C 0) * ν (Prod.snd '' C) := by
      rw [lintegral_indicator hP.measurableSet]
      simp

/-- A proved measure-preserving direct-sum coordinate map transports the bound for the
original body, keeping the actual image, actual central section and actual projection. -/
theorem measure_le_central_mul_projection_of_measurePreserving
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    (e : V ≃L[ℝ] U × W) (κ : Measure V)
    (μ : Measure U) [μ.IsAddHaarMeasure] (ν : Measure W) [SFinite ν]
    (he : MeasurePreserving e κ (μ.prod ν))
    {C : Set V} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ z ∈ C, -z ∈ C) :
    κ C ≤ μ (sectionAt (e '' C) 0) * ν (Prod.snd '' (e '' C)) := by
  have hI : IsCompact (e '' C) := hcompact.image e.continuous
  have hEq : (μ.prod ν) (e '' C) = κ C := by
    have h := he.measure_preimage hI.measurableSet.nullMeasurableSet
    simpa only [Set.preimage_image_eq _ e.injective] using h.symm
  rw [← hEq]
  apply measure_prod_le_central_mul_projection μ ν hI (hconvex.linear_image e.toLinearMap)
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨-v, hsymm v hv, map_neg e v⟩

end Haar

section FiniteCoordinates

variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The literal finite-coordinate specialization of central-section maximality. -/
theorem volume_sectionAt_le_central_fin (n : ℕ)
    {C : Set ((Fin n → ℝ) × W)} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ z ∈ C, -z ∈ C) (w : W) :
    volume (sectionAt C w) ≤ volume (sectionAt C 0) :=
  measure_sectionAt_le_central volume hcompact hconvex hsymm w

end FiniteCoordinates

end ArakelovGeometry.ConvexCentralSection

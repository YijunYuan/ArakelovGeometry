/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.Order.IntermediateValue

/-! # Actual slices and section volumes of original compact convex bodies -/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.ConvexBodySlices

open Set MeasureTheory Topology
open scoped ENNReal

variable {E : Type*}

/-- The literal section of a subset of `ℝ × E` at its first coordinate. -/
def slice (C : Set (ℝ × E)) (x : ℝ) : Set E := Prod.mk x ⁻¹' C

/-- The extended volume of a literal section. -/
def sectionVolume [MeasurableSpace E] (μ : Measure E) (C : Set (ℝ × E))
    (x : ℝ) : ℝ≥0∞ := μ (slice C x)

/-- The real volume of a literal section; compact sections have finite volume. -/
def sectionDensity [MeasurableSpace E] (μ : Measure E) (C : Set (ℝ × E))
    (x : ℝ) : ℝ := (sectionVolume μ C x).toReal

@[simp] theorem mem_slice {C : Set (ℝ × E)} {x : ℝ} {u : E} :
    u ∈ slice C x ↔ (x, u) ∈ C := Iff.rfl

theorem slice_eq_empty_of_not_mem_projection {C : Set (ℝ × E)} {x : ℝ}
    (hx : x ∉ Prod.fst '' C) : slice C x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact hx ⟨(x, u), hu, rfl⟩

section MeasureOnly

variable [MeasurableSpace E]

theorem sectionDensity_nonneg (μ : Measure E) (C : Set (ℝ × E)) (x : ℝ) :
    0 ≤ sectionDensity μ C x := ENNReal.toReal_nonneg

theorem sectionDensity_eq_zero_of_not_mem_projection (μ : Measure E)
    {C : Set (ℝ × E)} {x : ℝ} (hx : x ∉ Prod.fst '' C) : sectionDensity μ C x = 0 := by
  simp [sectionDensity, sectionVolume, slice_eq_empty_of_not_mem_projection hx]

end MeasureOnly

section Convex

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smul_add_mem_slice {C : Set (ℝ × E)} (hC : Convex ℝ C)
    {x y : ℝ} {u v : E} (hu : u ∈ slice C x) (hv : v ∈ slice C y)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) :
    r • u + s • v ∈ slice C (r * x + s * y) := by
  exact hC hu hv hr hs hrs

theorem convex_slice {C : Set (ℝ × E)} (hC : Convex ℝ C) (x : ℝ) :
    Convex ℝ (slice C x) := by
  intro u hu v hv r s hr hs hrs
  have h := smul_add_mem_slice hC hu hv hr hs hrs
  simpa [← add_mul, hrs] using h

/-- A nonempty convex interior projects onto the interior of the actual projection. -/
theorem projection_interior {C : Set (ℝ × E)} (hC : Convex ℝ C)
    (hne : (interior C).Nonempty) :
    Prod.fst '' interior C = interior (Prod.fst '' C) := by
  let D : Set ℝ := Prod.fst '' interior C
  have hDopen : IsOpen D := isOpenMap_fst _ isOpen_interior
  have hDconvex : Convex ℝ D := hC.interior.linear_image (LinearMap.fst ℝ ℝ E)
  have hDne : (interior D).Nonempty := by
    rw [hDopen.interior_eq]
    exact hne.image Prod.fst
  have hsub : Prod.fst '' C ⊆ closure D := by
    have hsub' : C ⊆ closure (interior C) := by
      rw [hC.closure_interior_eq_closure_of_nonempty_interior hne]
      exact subset_closure
    exact (image_mono hsub').trans (image_closure_subset_closure_image continuous_fst)
  apply Subset.antisymm (isOpenMap_fst.image_interior_subset C)
  have h := interior_mono hsub
  rwa [hDconvex.interior_closure_eq_interior_of_nonempty_interior hDne,
    hDopen.interior_eq] at h

/-- The actual projection of a nonempty compact convex body is its closed extrema interval. -/
theorem projection_eq_Icc {C : Set (ℝ × E)} (hC : IsCompact C)
    (hconvex : Convex ℝ C) (hne : C.Nonempty) :
    Prod.fst '' C = Icc (sInf (Prod.fst '' C)) (sSup (Prod.fst '' C)) := by
  exact eq_Icc_of_connected_compact
    ⟨hne.image Prod.fst, (hconvex.linear_image (LinearMap.fst ℝ ℝ E)).isPreconnected⟩
    (hC.image continuous_fst)

/-- A body with ambient interior has a nondegenerate projection interval. -/
theorem projection_lower_lt_upper {C : Set (ℝ × E)} (hC : IsCompact C)
    (hconvex : Convex ℝ C) (hne : (interior C).Nonempty) :
    sInf (Prod.fst '' C) < sSup (Prod.fst '' C) := by
  have hproj : (interior (Prod.fst '' C)).Nonempty := by
    rw [← projection_interior hconvex hne]
    exact hne.image Prod.fst
  rw [projection_eq_Icc hC hconvex (hne.mono interior_subset), interior_Icc] at hproj
  exact nonempty_Ioo.mp hproj

/-- At an interior projection coordinate, ambient interior and section interior agree. -/
theorem slice_interior {C : Set (ℝ × E)} (hC : Convex ℝ C)
    (hne : (interior C).Nonempty) {x : ℝ} (hx : x ∈ interior (Prod.fst '' C)) :
    slice (interior C) x = interior (slice C x) := by
  let D := slice (interior C) x
  have hDopen : IsOpen D := isOpen_interior.preimage (Continuous.prodMk_right x)
  have hDconvex : Convex ℝ D := convex_slice hC.interior x
  have hDne : D.Nonempty := by
    rw [← projection_interior hC hne] at hx
    obtain ⟨⟨y, v⟩, hv, hyx⟩ := hx
    dsimp at hyx
    subst y
    exact ⟨v, hv⟩
  have hsub : slice C x ⊆ closure D := by
    obtain ⟨v, hv⟩ := hDne
    intro u hu
    have hsegment : openSegment ℝ u v ⊆ D := by
      rintro _ ⟨r, t, hr, ht, hrt, rfl⟩
      have hm := hC.combo_self_interior_mem_interior hu hv hr.le ht hrt
      change (x, r • u + t • v) ∈ interior C
      convert hm using 1; simp [← add_mul, hrt]
    exact (closure_mono hsegment) (segment_subset_closure_openSegment (left_mem_segment ℝ u v))
  apply Subset.antisymm (preimage_interior_subset_interior_preimage (Continuous.prodMk_right x))
  have hi := interior_mono hsub
  have hDint : (interior D).Nonempty := by rwa [hDopen.interior_eq]
  rwa [hDconvex.interior_closure_eq_interior_of_nonempty_interior hDint,
    hDopen.interior_eq] at hi

/-- Off the frontier of an interior-coordinate slice, slice indicators are locally constant. -/
theorem continuousAt_slice_indicator {C : Set (ℝ × E)} (hclosed : IsClosed C)
    (hC : Convex ℝ C) (hne : (interior C).Nonempty) {x : ℝ}
    (hx : x ∈ interior (Prod.fst '' C)) {u : E} (hu : u ∉ frontier (slice C x)) :
    ContinuousAt (fun y => (slice C y).indicator (fun _ => (1 : ℝ)) u) x := by
  classical
  by_cases hmem : u ∈ slice C x
  · have hi : u ∈ interior (slice C x) := by
      by_contra hi
      exact hu ⟨subset_closure hmem, hi⟩
    have ha : (x, u) ∈ interior C := by
      change u ∈ slice (interior C) x
      rwa [slice_interior hC hne hx]
    have he : ∀ᶠ y in 𝓝 x, (y, u) ∈ interior C :=
      (Continuous.prodMk_left u).continuousAt.eventually (isOpen_interior.mem_nhds ha)
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    have hyC : (y, u) ∈ C := interior_subset hy
    exact indicator_of_mem (s := slice C y) hyC _
  · have he : ∀ᶠ y in 𝓝 x, (y, u) ∈ Cᶜ :=
      (Continuous.prodMk_left u).continuousAt.eventually (hclosed.isOpen_compl.mem_nhds hmem)
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    exact indicator_of_notMem (show u ∉ slice C y from hy) _

end Convex

variable [NormedAddCommGroup E]

/-- A compact set has compact literal sections, including empty sections. -/
theorem isCompact_slice {C : Set (ℝ × E)} (hC : IsCompact C) (x : ℝ) :
    IsCompact (slice C x) := by
  exact (Function.LeftInverse.isClosedEmbedding (f := Prod.snd) (g := Prod.mk x)
    (fun _ => rfl) continuous_snd (Continuous.prodMk_right x)).isCompact_preimage hC

theorem interior_slice_nonempty_of_mem_interior {C : Set (ℝ × E)} {x : ℝ} {u : E}
    (hu : (x, u) ∈ interior C) : (interior (slice C x)).Nonempty := by
  exact ⟨u, preimage_interior_subset_interior_preimage (Continuous.prodMk_right x) hu⟩

variable [MeasurableSpace E]

theorem sectionVolume_lt_top (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {C : Set (ℝ × E)} (hC : IsCompact C) (x : ℝ) : sectionVolume μ C x < ⊤ :=
  (isCompact_slice hC x).measure_lt_top

theorem hasCompactSupport_sectionDensity (μ : Measure E)
    {C : Set (ℝ × E)} (hC : IsCompact C) : HasCompactSupport (sectionDensity μ C) := by
  exact HasCompactSupport.intro (hC.image continuous_fst)
    (fun _ hx => sectionDensity_eq_zero_of_not_mem_projection μ hx)

/-- Ambient interior produces positive volume in the actual slice. -/
theorem sectionDensity_pos_of_mem_interior (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    [μ.IsOpenPosMeasure] {C : Set (ℝ × E)} (hC : IsCompact C) {x : ℝ} {u : E}
    (hu : (x, u) ∈ interior C) : 0 < sectionDensity μ C x := by
  apply ENNReal.toReal_pos _ (sectionVolume_lt_top μ hC x).ne
  exact ne_of_gt ((isOpen_interior.measure_pos μ
    (interior_slice_nonempty_of_mem_interior hu)).trans_le (measure_mono interior_subset))

/-- Every point in the open projection has positive actual section density. -/
theorem sectionDensity_pos_on_interior_projection [NormedSpace ℝ E] (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {C : Set (ℝ × E)} (hC : IsCompact C) (hconvex : Convex ℝ C)
    (hne : (interior C).Nonempty) {x : ℝ} (hx : x ∈ interior (Prod.fst '' C)) :
    0 < sectionDensity μ C x := by
  rw [← projection_interior hconvex hne] at hx
  obtain ⟨⟨y, u⟩, hu, hxy⟩ := hx
  dsimp at hxy
  subst y
  exact sectionDensity_pos_of_mem_interior μ hC hu

/-- Positivity on the actual projection extrema interval, ready for density transport. -/
theorem sectionDensity_pos_on_Ioo [NormedSpace ℝ E] (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {C : Set (ℝ × E)} (hC : IsCompact C) (hconvex : Convex ℝ C)
    (hne : (interior C).Nonempty) {x : ℝ}
    (hx : x ∈ Ioo (sInf (Prod.fst '' C)) (sSup (Prod.fst '' C))) :
    0 < sectionDensity μ C x := by
  apply sectionDensity_pos_on_interior_projection μ hC hconvex hne
  rwa [projection_eq_Icc hC hconvex (hne.mono interior_subset), interior_Icc]

variable [BorelSpace E] [SecondCountableTopology E]

/-- The section measure is genuinely measurable, rather than an assumed density. -/
theorem measurable_sectionVolume (μ : Measure E) [SFinite μ]
    {C : Set (ℝ × E)} (hC : IsCompact C) : Measurable (sectionVolume μ C) :=
  measurable_measure_prodMk_left hC.isClosed.measurableSet

theorem measurable_sectionDensity (μ : Measure E) [SFinite μ]
    {C : Set (ℝ × E)} (hC : IsCompact C) : Measurable (sectionDensity μ C) :=
  (measurable_sectionVolume μ hC).ennreal_toReal

/-- Tonelli disintegrates the measure of the original set over its literal sections. -/
theorem lintegral_sectionVolume (ν : Measure ℝ) (μ : Measure E) [SFinite μ]
    {C : Set (ℝ × E)} (hC : IsCompact C) :
    ∫⁻ x, sectionVolume μ C x ∂ν = (ν.prod μ) C :=
  (Measure.prod_apply hC.isClosed.measurableSet).symm

/-- The real section density integrates to the real volume of the original body. -/
theorem integral_sectionDensity (ν : Measure ℝ) (μ : Measure E) [SFinite μ]
    [IsFiniteMeasureOnCompacts μ] {C : Set (ℝ × E)} (hC : IsCompact C) :
    ∫ x, sectionDensity μ C x ∂ν = ((ν.prod μ) C).toReal := by
  change (∫ x, (sectionVolume μ C x).toReal ∂ν) = _
  rw [integral_toReal (measurable_sectionVolume μ hC).aemeasurable
    (Filter.Eventually.of_forall (sectionVolume_lt_top μ hC)), lintegral_sectionVolume ν μ hC]

/-- Finite product volume yields an integrable actual section density. -/
theorem integrable_sectionDensity (ν : Measure ℝ) (μ : Measure E) [SFinite μ]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {C : Set (ℝ × E)} (hC : IsCompact C) : Integrable (sectionDensity μ C) ν := by
  apply (integrable_toReal_iff (measurable_sectionVolume μ hC).aemeasurable
    (Filter.Eventually.of_forall fun x => (sectionVolume_lt_top μ hC x).ne)).mpr
  rw [lintegral_sectionVolume ν μ hC]
  exact hC.measure_lt_top.ne

/-- Fubini on the open projection interval; the endpoint sections have zero base measure. -/
theorem integral_sectionDensity_Ioo [NormedSpace ℝ E] (ν : Measure ℝ) (μ : Measure E)
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] [NullSingletonClass ν]
    {C : Set (ℝ × E)} (hC : IsCompact C) (hconvex : Convex ℝ C) (hne : C.Nonempty) :
    ∫ x in Ioo (sInf (Prod.fst '' C)) (sSup (Prod.fst '' C)), sectionDensity μ C x ∂ν =
      ((ν.prod μ) C).toReal := by
  rw [setIntegral_congr_set Ioo_ae_eq_Icc]
  rw [← projection_eq_Icc hC hconvex hne]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun _ hx => sectionDensity_eq_zero_of_not_mem_projection μ hx)]
  exact integral_sectionDensity ν μ hC

/-- Actual section densities are interval integrable on every finite interval. -/
theorem intervalIntegrable_sectionDensity (ν : Measure ℝ) (μ : Measure E) [SFinite μ]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {C : Set (ℝ × E)} (hC : IsCompact C) (a b : ℝ) :
    IntervalIntegrable (sectionDensity μ C) ν a b :=
  (integrable_sectionDensity ν μ hC).intervalIntegrable

/-- The actual interval integral equals the volume of the original compact convex body. -/
theorem intervalIntegral_sectionDensity [NormedSpace ℝ E] (ν : Measure ℝ) (μ : Measure E)
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] [NullSingletonClass ν]
    {C : Set (ℝ × E)} (hC : IsCompact C) (hconvex : Convex ℝ C) (hne : C.Nonempty) :
    ∫ x in (sInf (Prod.fst '' C))..(sSup (Prod.fst '' C)), sectionDensity μ C x ∂ν =
      ((ν.prod μ) C).toReal := by
  have hab : sInf (Prod.fst '' C) ≤ sSup (Prod.fst '' C) := by
    apply nonempty_Icc.mp
    rw [← projection_eq_Icc hC hconvex hne]
    exact hne.image Prod.fst
  rw [intervalIntegral.integral_of_le hab, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
  exact integral_sectionDensity_Ioo ν μ hC hconvex hne

omit [SecondCountableTopology E] in
/-- Actual Haar section volume is continuous at every interior projection coordinate. -/
theorem continuousAt_sectionDensity [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {C : Set (ℝ × E)} (hC : IsCompact C)
    (hconvex : Convex ℝ C) (hne : (interior C).Nonempty) {x : ℝ}
    (hx : x ∈ interior (Prod.fst '' C)) : ContinuousAt (sectionDensity μ C) x := by
  classical
  let K := Prod.snd '' C
  have hK : IsCompact K := hC.image continuous_snd
  have hmeas : ∀ y, AEStronglyMeasurable ((slice C y).indicator (fun _ => (1 : ℝ))) μ :=
    fun y => aestronglyMeasurable_const.indicator (isCompact_slice hC y).measurableSet
  have hbound : ∀ y u, ‖(slice C y).indicator (fun _ => (1 : ℝ)) u‖ ≤
      K.indicator (fun _ => (1 : ℝ)) u := by
    intro y u
    by_cases hu : u ∈ slice C y
    · have huK : u ∈ K := ⟨(y, u), hu, rfl⟩
      simp only [indicator_of_mem hu, indicator_of_mem huK, norm_one, le_refl]
    · rw [indicator_of_notMem hu, norm_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) u
  have hboundi : Integrable (K.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const hK.measure_lt_top.ne)
  have hfrontier : ∀ᵐ u ∂μ, u ∉ frontier (slice C x) := by
    apply ae_iff.mpr
    simpa using (convex_slice hconvex x).addHaar_frontier μ
  have hcont : ∀ᵐ u ∂μ,
      ContinuousAt (fun y => (slice C y).indicator (fun _ => (1 : ℝ)) u) x :=
    hfrontier.mono fun u hu => continuousAt_slice_indicator hC.isClosed hconvex hne hx hu
  have hrep : ∀ y, (∫ u, (slice C y).indicator (fun _ => (1 : ℝ)) u ∂μ) =
      sectionDensity μ C y := by
    intro y
    exact integral_indicator_one (isCompact_slice hC y).measurableSet
  have h := continuousAt_of_dominated (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall fun y => Filter.Eventually.of_forall (hbound y)) hboundi hcont
  simpa only [hrep] using h

omit [SecondCountableTopology E] in
/-- Actual Haar slice density is continuous on the original open projection interval. -/
theorem continuousOn_sectionDensity_Ioo [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {C : Set (ℝ × E)} (hC : IsCompact C)
    (hconvex : Convex ℝ C) (hne : (interior C).Nonempty) :
    ContinuousOn (sectionDensity μ C)
      (Ioo (sInf (Prod.fst '' C)) (sSup (Prod.fst '' C))) := by
  intro x hx
  apply (continuousAt_sectionDensity μ hC hconvex hne ?_).continuousWithinAt
  rwa [projection_eq_Icc hC hconvex (hne.mono interior_subset), interior_Icc]

end ArakelovGeometry.ConvexBodySlices

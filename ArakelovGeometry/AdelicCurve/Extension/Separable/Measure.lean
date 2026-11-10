/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Separable.FibreIntegral
import ArakelovGeometry.AdelicCurve.Extension.Separable.Measurability
import Mathlib.CategoryTheory.Category.Init

/-!
# The induced measure for a finite separable extension

The induced measure, nonnegative and signed disintegration, and projection
pushforward (Chen–Moriwaki, Definition 3.3.6 and Theorem 3.3.7(1–3)).
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u v w

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (L : Type w) [Field L] [Algebra K L]

variable [FiniteDimensional K L] [_s : Algebra.IsSeparable K L]

/-- Chen--Moriwaki, Definition 3.3.6: the measure `ν_L` on `Ω_L` defined by
`ν_L(A) = ∫_{Ω_K} I_{L/K}(1_A) dν_K`. -/
noncomputable def inducedMeasure : Measure (ParameterSpaceExtension AS L) :=
  Measure.ofMeasurable
    (fun A _hA ↦ ∫⁻ ω, fibreLIntegral AS L (Set.indicator A fun _ ↦ (1 : ℝ≥0∞)) ω ∂AS.v)
    (by simp [fibreLIntegral])
    (by
      intro A hA hdisj
      have hind (s : Set (ParameterSpaceExtension AS L)) (hs : MeasurableSet s) (ω : AS.Ω) :
          fibreLIntegral AS L (s.indicator fun _ ↦ 1) ω =
            fibreProbabilityMeasure AS L ω (Subtype.val ⁻¹' s) := by
        simp only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def]
        rw [lintegral_indicator_const (hs.preimage measurable_subtype_coe)]
        simp
      have hpoint (ω : AS.Ω) :
          fibreLIntegral AS L ((⋃ n, A n).indicator fun _ ↦ 1) ω =
            ∑' n, fibreLIntegral AS L ((A n).indicator fun _ ↦ 1) ω := by
        rw [hind _ (MeasurableSet.iUnion hA), Set.preimage_iUnion,
          measure_iUnion (fun i j hij ↦ (hdisj hij).preimage Subtype.val)
            (fun n ↦ (hA n).preimage measurable_subtype_coe)]
        congr 1
        funext n
        exact (hind _ (hA n) ω).symm
      simp_rw [hpoint]
      exact lintegral_tsum (fun n ↦
        (measurable_fibreLIntegral AS L (measurable_const.indicator (hA n))).aemeasurable))

/-- The defining formula of Definition 3.3.6. -/
theorem inducedMeasure_apply {A : Set (ParameterSpaceExtension AS L)} (hA : MeasurableSet A) :
    inducedMeasure AS L A =
      ∫⁻ ω, fibreLIntegral AS L (Set.indicator A fun _ ↦ (1 : ℝ≥0∞)) ω ∂AS.v :=
  Measure.ofMeasurable_apply A hA

/-- Chen--Moriwaki, Theorem 3.3.7(1), formula (3.7): the induced measure integrates
nonnegative measurable functions through the fibre integration operator. -/
theorem lintegral_inducedMeasure {f : ParameterSpaceExtension AS L → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂inducedMeasure AS L = ∫⁻ ω, fibreLIntegral AS L f ω ∂AS.v := by
  refine Measurable.ennreal_induction
    (motive := fun f ↦ (∫⁻ x, f x ∂inducedMeasure AS L) =
      ∫⁻ ω, fibreLIntegral AS L f ω ∂AS.v) ?_ ?_ ?_ hf
  · intro c s hs
    rw [lintegral_indicator_const hs, inducedMeasure_apply AS L hs,
      ← lintegral_const_mul c (measurable_fibreLIntegral AS L (measurable_const.indicator hs))]
    apply lintegral_congr
    intro ω
    simp only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def]
    rw [lintegral_indicator_const (hs.preimage measurable_subtype_coe),
      lintegral_indicator_const (hs.preimage measurable_subtype_coe), one_mul]
  · intro f g _ hf hg ihf ihg
    simp only [Pi.add_apply]
    rw [lintegral_add_left hf, ihf, ihg,
      ← lintegral_add_left (measurable_fibreLIntegral AS L hf)]
    apply lintegral_congr
    intro ω
    exact (lintegral_add_left (hf.comp measurable_subtype_coe) _).symm
  · intro f hf hmono ih
    rw [lintegral_iSup hf hmono]
    simp_rw [ih]
    rw [← lintegral_iSup (fun n ↦ measurable_fibreLIntegral AS L (hf n))
      (fun n m h ω ↦ lintegral_mono (fun x ↦ hmono h x.val))]
    apply lintegral_congr
    intro ω
    exact (lintegral_iSup (fun n ↦ (hf n).comp measurable_subtype_coe)
      (fun n m h x ↦ hmono h x.val)).symm

/-- Chen--Moriwaki, Theorem 3.3.7(2): a measurable function is integrable for the induced
measure if and only if the fibre integral of its absolute value is integrable on the base. -/
theorem integrable_inducedMeasure_iff {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable f) :
    Integrable f (inducedMeasure AS L) ↔
      Integrable (fibreIntegral AS L fun x ↦ |f x|) AS.v := by
  have habs : Measurable (fun x ↦ |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hnonneg (ω : AS.Ω) : 0 ≤ fibreIntegral AS L (fun x ↦ |f x|) ω :=
    integral_nonneg (fun x ↦ abs_nonneg (f x.val))
  have heq (ω : AS.Ω) :
      ENNReal.ofReal (fibreIntegral AS L (fun x ↦ |f x|) ω) =
        fibreLIntegral AS L (fun x ↦ ENNReal.ofReal |f x|) ω :=
    ofReal_integral_eq_lintegral_ofReal (integrable_fibre AS L ω _)
      (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x.val))
  rw [← integrable_norm_iff hf.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]
  rw [← lintegral_ofReal_ne_top_iff_integrable habs.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x)),
    lintegral_inducedMeasure AS L habs.ennreal_ofReal,
    ← lintegral_ofReal_ne_top_iff_integrable
      (measurable_fibreIntegral AS L habs).aestronglyMeasurable
      (Filter.Eventually.of_forall hnonneg)]
  simp_rw [heq]

/-- A globally almost everywhere property holds almost everywhere on almost every fibre. -/
theorem ae_ae_fibre_of_ae {p : ParameterSpaceExtension AS L → Prop}
    (hp : ∀ᵐ x ∂inducedMeasure AS L, p x) :
    ∀ᵐ ω ∂AS.v, ∀ᵐ x ∂fibreProbabilityMeasure AS L ω, p x.val := by
  obtain ⟨N, hsub, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  rw [inducedMeasure_apply AS L hN] at hzero
  have h := (lintegral_eq_zero_iff
    (measurable_fibreLIntegral AS L (measurable_const.indicator hN))).mp hzero
  filter_upwards [h] with ω hω
  apply ae_iff.mpr
  apply measure_mono_null (t := Subtype.val ⁻¹' N) (fun x hx ↦ hsub hx)
  change fibreProbabilityMeasure AS L ω (Subtype.val ⁻¹' N) = 0
  simpa only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def,
    lintegral_indicator_const (hN.preimage measurable_subtype_coe), one_mul,
    Pi.zero_apply] using hω

/-- Chen--Moriwaki, Theorem 3.3.7(2): formula (3.7) also holds for integrable real-valued
functions. -/
theorem integral_inducedMeasure {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable f (inducedMeasure AS L)) :
    ∫ x, f x ∂inducedMeasure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
  have hnonnegative {f : ParameterSpaceExtension AS L → ℝ}
      (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) :
      ∫ x, f x ∂inducedMeasure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
    have heq (ω : AS.Ω) :
        ENNReal.ofReal (fibreIntegral AS L f ω) =
          fibreLIntegral AS L (fun x ↦ ENNReal.ofReal (f x)) ω :=
      ofReal_integral_eq_lintegral_ofReal (integrable_fibre AS L ω _)
        (Filter.Eventually.of_forall fun x ↦ hpos x.val)
    have hnonneg (ω : AS.Ω) : 0 ≤ fibreIntegral AS L f ω :=
      integral_nonneg (fun x ↦ hpos x.val)
    rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall hpos) hf.aestronglyMeasurable,
      lintegral_inducedMeasure AS L hf.ennreal_ofReal,
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall hnonneg)
        (measurable_fibreIntegral AS L hf).aestronglyMeasurable]
    simp_rw [heq]
  have hmeasurable {f : ParameterSpaceExtension AS L → ℝ}
      (hf : Integrable f (inducedMeasure AS L)) (hfm : Measurable f) :
      ∫ x, f x ∂inducedMeasure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
    let p := fun x ↦ max (f x) 0
    let n := fun x ↦ max (-f x) 0
    have hp : Measurable p := hfm.max measurable_const
    have hn : Measurable n := hfm.neg.max measurable_const
    have hip : Integrable p (inducedMeasure AS L) := hf.pos_part
    have hin : Integrable n (inducedMeasure AS L) := hf.neg.pos_part
    have hbp : Integrable (fibreIntegral AS L p) AS.v := by
      have h := (integrable_inducedMeasure_iff AS L hp).mp hip
      simpa only [p, abs_of_nonneg (le_max_right (f _) (0 : ℝ))] using h
    have hbn : Integrable (fibreIntegral AS L n) AS.v := by
      have h := (integrable_inducedMeasure_iff AS L hn).mp hin
      simpa only [n, abs_of_nonneg (le_max_right (-f _) (0 : ℝ))] using h
    have hfsub : f = p - n := by
      funext x
      dsimp [p, n]
      grind
    have hsub : fibreIntegral AS L f =
        fibreIntegral AS L p - fibreIntegral AS L n := by
      funext ω
      rw [hfsub]
      exact integral_sub (integrable_fibre AS L ω _) (integrable_fibre AS L ω _)
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [integral_sub hbp hbn, ← hnonnegative hp (fun _ ↦ le_max_right _ _),
      ← hnonnegative hn (fun _ ↦ le_max_right _ _), hfsub]
    simpa only [Pi.sub_apply] using integral_sub hip hin
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[inducedMeasure AS L] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g (inducedMeasure AS L) := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfib : fibreIntegral AS L f =ᵐ[AS.v] fibreIntegral AS L g := by
    filter_upwards [ae_ae_fibre_of_ae AS L hfg] with ω hω
    exact integral_congr_ae hω
  exact (integral_congr_ae hfg).trans
    ((hmeasurable hg hgm).trans (integral_congr_ae hfib).symm)

/-- The projection sends the induced measure to the base measure. -/
theorem map_inducedMeasure_proj :
    Measure.map (ParameterSpaceExtension.proj (AS := AS) (L := L)) (inducedMeasure AS L) =
      AS.v := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_proj AS L) hs, inducedMeasure_apply AS L
    (hs.preimage (measurable_proj AS L))]
  have hconst (ω : AS.Ω) :
      fibreLIntegral AS L ((proj ⁻¹' s).indicator fun _ ↦ 1) ω =
        s.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
    change (∫⁻ x : ExtensionFiber AS L ω,
      (proj ⁻¹' s).indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val
        ∂fibreProbabilityMeasure AS L ω) = _
    classical
    simp only [Set.indicator, Set.mem_preimage]
    simp_rw [show ∀ x : ExtensionFiber AS L ω, x.val.proj = ω from fun x ↦ x.property]
    simp
  simp_rw [hconst]
  rw [lintegral_indicator_const hs, one_mul]

/-- Chen--Moriwaki, Theorem 3.3.7(3), formula (3.8): integrating a pullback from the base
against the induced measure is integrating against the base measure. -/
theorem integral_comp_proj_inducedMeasure {φ : AS.Ω → ℝ} (hφ : Integrable φ AS.v) :
    ∫ x, φ (proj x) ∂inducedMeasure AS L = ∫ ω, φ ω ∂AS.v := by
  have hm : AEStronglyMeasurable φ
      (Measure.map (proj (AS := AS) (L := L)) (inducedMeasure AS L)) := by
    rw [map_inducedMeasure_proj AS L]
    exact hφ.aestronglyMeasurable
  have h := integral_map (measurable_proj AS L).aemeasurable hm
  rw [map_inducedMeasure_proj AS L] at h
  exact h.symm

end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

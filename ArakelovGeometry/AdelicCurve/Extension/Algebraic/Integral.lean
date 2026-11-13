/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Measure
import Mathlib.CategoryTheory.Category.Init

/-!
# Integration over algebraic extensions

Disintegration, integrability, almost everywhere fibre statements and pullback
formulas for the algebraic extension measure, following Proposition 3.4.9.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.Algebraic

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u w

variable {K : Type u} [Field K] (AS : AdelicStructure K)
variable (L : Type w) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Chen--Moriwaki, Proposition 3.4.9: a projectively measurable function is `ν_L`-integrable
if and only if the fibre integral of its absolute value — computed in `[0, +∞]`, as in the
discussion after Proposition 3.4.8, since fibres of an infinite extension need not have
integrable restrictions — has finite integral on the base. -/
theorem integrable_measure_iff {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) :
    Integrable[projectiveMeasurableSpace AS L] f (measure AS L) ↔
      ∫⁻ ω, fibreLIntegral AS L (fun x ↦ ENNReal.ofReal |f x|) ω ∂AS.v < ∞ := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have habs : Measurable (fun x ↦ |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  rw [← integrable_norm_iff hf.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]
  rw [← lintegral_ofReal_ne_top_iff_integrable habs.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x)),
    lintegral_measure AS L habs.ennreal_ofReal]
  exact lt_top_iff_ne_top.symm

/-- An almost everywhere property holds almost everywhere on almost every algebraic fibre. -/
theorem ae_ae_fibre_of_ae {p : ParameterSpaceExtension AS L → Prop}
    (hp : ∀ᵐ x ∂measure AS L, p x) :
    ∀ᵐ ω ∂AS.v, ∀ᵐ x ∂fibreProbabilityMeasure AS L ω, p x.val := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  obtain ⟨N, hsub, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  rw [measure_apply AS L hN] at hzero
  have h := (lintegral_eq_zero_iff
    (measurable_fibreLIntegral AS L (measurable_const.indicator hN))).mp hzero
  filter_upwards [h] with ω hω
  apply ae_iff.mpr
  apply measure_mono_null (t := Subtype.val ⁻¹' N) (fun x hx ↦ hsub hx)
  change fibreProbabilityMeasure AS L ω (Subtype.val ⁻¹' N) = 0
  simpa only [fibreLIntegral, ← Set.indicator_comp_right, Function.comp_def,
    lintegral_indicator_const (hN.preimage (measurable_subtype_val_baseFiber AS L ω)), one_mul,
    Pi.zero_apply] using hω

/-- A globally null set has null intersection with almost every algebraic fibre. -/
theorem ae_fibre_measure_preimage_eq_zero {N : Set (ParameterSpaceExtension AS L)}
    (hN : measure AS L N = 0) :
    ∀ᵐ ω ∂AS.v, fibreProbabilityMeasure AS L ω (Subtype.val ⁻¹' N) = 0 := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have h : ∀ᵐ x ∂measure AS L, x ∉ N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hN
  filter_upwards [ae_ae_fibre_of_ae AS L h] with ω hω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  simpa only [ae_iff, not_not, Set.preimage] using hω

/-- The real integral of a nonnegative measurable function is the real value of its
nonnegative integral. -/
theorem fibreIntegral_eq_toReal_of_nonneg {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) (hpos : ∀ x, 0 ≤ f x)
    (ω : AS.Ω) :
    fibreIntegral AS L f ω =
      (fibreLIntegral AS L (fun x ↦ ENNReal.ofReal (f x)) ω).toReal := by
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x ↦ hpos x.val)
    (measurable_restrict_baseFiber AS L hf ω).aestronglyMeasurable

/-- A measurable integrable function has integrable restrictions to almost every algebraic fibre. -/
theorem integrable_fibre_ae_of_measurable {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f)
    (hi : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∀ᵐ ω ∂AS.v, Integrable (fun x : BaseFiber L ω ↦ f x.val)
      (fibreProbabilityMeasure AS L ω) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have habs : Measurable (fun x ↦ ENNReal.ofReal |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm.ennreal_ofReal
  have hfin := (integrable_measure_iff AS L hf).mp hi
  filter_upwards [ae_lt_top (measurable_fibreLIntegral AS L habs) hfin.ne] with ω hω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  have hm := measurable_restrict_baseFiber AS L hf ω
  rw [← integrable_norm_iff hm.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]
  apply (lintegral_ofReal_ne_top_iff_integrable
    (μ := fibreProbabilityMeasure AS L ω) (f := fun x : BaseFiber L ω ↦ |f x.val|)
    (by simpa only [Real.norm_eq_abs] using hm.norm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x.val))).mp
  exact hω.ne

/-- The average of a nonnegative integrable function is integrable on the base. -/
theorem integrable_fibreIntegral_of_nonneg {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) (hpos : ∀ x, 0 ≤ f x)
    (hi : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    Integrable (fibreIntegral AS L f) AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have hfin := (integrable_measure_iff AS L hf).mp hi
  simp_rw [abs_of_nonneg (hpos _)] at hfin
  have heq : fibreIntegral AS L f =
      fun ω ↦ (fibreLIntegral AS L (fun x ↦ ENNReal.ofReal (f x)) ω).toReal :=
    funext (fibreIntegral_eq_toReal_of_nonneg AS L hf hpos)
  rw [heq]
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_fibreLIntegral AS L hf.ennreal_ofReal).aemeasurable hfin.ne

/-- Nonnegative integrable real functions satisfy the algebraic disintegration formula. -/
theorem integral_measure_of_nonneg {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f) (hpos : ∀ x, 0 ≤ f x)
    (hi : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∫ x, f x ∂measure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have hfin := (integrable_measure_iff AS L hf).mp hi
  simp_rw [abs_of_nonneg (hpos _)] at hfin
  have hm := measurable_fibreLIntegral AS L hf.ennreal_ofReal
  have heq : fibreIntegral AS L f =
      fun ω ↦ (fibreLIntegral AS L (fun x ↦ ENNReal.ofReal (f x)) ω).toReal :=
    funext (fibreIntegral_eq_toReal_of_nonneg AS L hf hpos)
  calc
    _ = (∫⁻ ω, fibreLIntegral AS L (fun x ↦ ENNReal.ofReal (f x)) ω ∂AS.v).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos)
        hf.aestronglyMeasurable, lintegral_measure AS L hf.ennreal_ofReal]
    _ = _ := by
      rw [heq, integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
        hm.ennreal_toReal.aestronglyMeasurable]
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_lt_top hm hfin.ne] with ω hω
      exact (ENNReal.ofReal_toReal hω.ne).symm

theorem integrable_fibreIntegral_and_integral_of_measurable
    {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Measurable[projectiveMeasurableSpace AS L] f)
    (hi : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    Integrable (fibreIntegral AS L f) AS.v ∧
      ∫ x, f x ∂measure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  let p := fun x ↦ max (f x) 0
  let n := fun x ↦ max (-f x) 0
  have hp : Measurable p := hf.max measurable_const
  have hn : Measurable n := hf.neg.max measurable_const
  have hip : Integrable p (measure AS L) := hi.pos_part
  have hin : Integrable n (measure AS L) := hi.neg.pos_part
  have hbp := integrable_fibreIntegral_of_nonneg AS L hp (fun _ ↦ le_max_right _ _) hip
  have hbn := integrable_fibreIntegral_of_nonneg AS L hn (fun _ ↦ le_max_right _ _) hin
  have hfsub : f = p - n := by
    funext x
    dsimp [p, n]
    grind
  have hsub : fibreIntegral AS L f =ᵐ[AS.v]
      fun ω ↦ fibreIntegral AS L p ω - fibreIntegral AS L n ω := by
    filter_upwards [integrable_fibre_ae_of_measurable AS L hp hip,
      integrable_fibre_ae_of_measurable AS L hn hin] with ω hωp hωn
    change (∫ x : BaseFiber L ω, f x.val ∂fibreProbabilityMeasure AS L ω) = _
    rw [hfsub]
    exact integral_sub hωp hωn
  refine ⟨(hbp.sub hbn).congr hsub.symm, ?_⟩
  rw [integral_congr_ae hsub, integral_sub hbp hbn,
    ← integral_measure_of_nonneg AS L hp (fun _ ↦ le_max_right _ _) hip,
    ← integral_measure_of_nonneg AS L hn (fun _ ↦ le_max_right _ _) hin, hfsub]
  exact integral_sub hip hin

/-- Integrable functions have integrable restrictions to almost every algebraic fibre. -/
theorem integrable_fibre_ae {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∀ᵐ ω ∂AS.v, Integrable (fun x : BaseFiber L ω ↦ f x.val)
      (fibreProbabilityMeasure AS L ω) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[measure AS L] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g (measure AS L) := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  filter_upwards [integrable_fibre_ae_of_measurable AS L hgm hg,
    ae_ae_fibre_of_ae AS L hfg] with ω hω hfgω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  apply hω.congr
  filter_upwards [hfgω] with x hx
  exact hx.symm

/-- Fibre averages of integrable functions are integrable on the base. -/
theorem integrable_fibreIntegral {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    Integrable (fibreIntegral AS L f) AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[measure AS L] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g (measure AS L) := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hi := (integrable_fibreIntegral_and_integral_of_measurable AS L hgm hg).1
  apply hi.congr
  filter_upwards [ae_ae_fibre_of_ae AS L hfg] with ω hω
  exact (integral_congr_ae hω).symm

/-- Chen--Moriwaki, Proposition 3.4.9: algebraic disintegration for integrable real functions. -/
theorem integral_measure {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∫ x, f x ∂measure AS L = ∫ ω, fibreIntegral AS L f ω ∂AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[measure AS L] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g (measure AS L) := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfib : fibreIntegral AS L f =ᵐ[AS.v] fibreIntegral AS L g := by
    filter_upwards [ae_ae_fibre_of_ae AS L hfg] with ω hω
    exact integral_congr_ae hω
  exact (integral_congr_ae hfg).trans
    (((integrable_fibreIntegral_and_integral_of_measurable AS L hgm hg).2).trans
      (integral_congr_ae hfib).symm)

/-- Chen--Moriwaki, Proposition 3.4.9: algebraic fibre integration is an L1 contraction. -/
theorem integral_abs_fibreIntegral_le {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∫ ω, |fibreIntegral AS L f ω| ∂AS.v ≤ ∫ x, |f x| ∂measure AS L := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have habs : Integrable (fun x ↦ |f x|) (measure AS L) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  rw [integral_measure AS L habs]
  apply integral_mono
  · simpa only [Real.norm_eq_abs] using (integrable_fibreIntegral AS L hf).norm
  · exact integrable_fibreIntegral AS L habs
  · intro ω
    let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
    simpa only [fibreIntegral, Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := fibreProbabilityMeasure AS L ω)
        (fun x : BaseFiber L ω ↦ f x.val)

theorem ofReal_abs_fibreIntegral_le_fibreLIntegral_ae
    {f : ParameterSpaceExtension AS L → ℝ}
    (hf : Integrable[projectiveMeasurableSpace AS L] f (measure AS L)) :
    ∀ᵐ ω ∂AS.v, ENNReal.ofReal |fibreIntegral AS L f ω| ≤
      fibreLIntegral AS L (fun x ↦ ENNReal.ofReal |f x|) ω := by
  filter_upwards [integrable_fibre_ae AS L hf] with ω hω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  have habs : Integrable (fun x : BaseFiber L ω ↦ |f x.val|)
      (fibreProbabilityMeasure AS L ω) := by
    simpa only [Real.norm_eq_abs] using hω.norm
  calc
    _ ≤ ENNReal.ofReal (fibreIntegral AS L (fun x ↦ |f x|) ω) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [fibreIntegral, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := fibreProbabilityMeasure AS L ω)
          (fun x : BaseFiber L ω ↦ f x.val)
    _ = _ := ofReal_integral_eq_lintegral_ofReal habs
      (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x.val))

/-- The base projection preserves the algebraic extension measure. -/
theorem map_measure_proj :
    (letI : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
    Measure.map ParameterSpaceExtension.proj (measure AS L) = AS.v) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_proj_projective AS L) hs, measure_apply AS L
    (hs.preimage (measurable_proj_projective AS L))]
  have hconst (ω : AS.Ω) :
      fibreLIntegral AS L ((ParameterSpaceExtension.proj ⁻¹' s).indicator fun _ ↦ 1) ω =
        s.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
    change (∫⁻ x : BaseFiber L ω,
      (ParameterSpaceExtension.proj ⁻¹' s).indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val
        ∂fibreProbabilityMeasure AS L ω) = _
    classical
    simp only [Set.indicator, Set.mem_preimage]
    simp_rw [show ∀ x : BaseFiber L ω, ParameterSpaceExtension.proj x.val = ω
      from fun x ↦ x.property]
    simp
  simp_rw [hconst]
  rw [lintegral_indicator_const hs, one_mul]

/-- Formula (3.21): the pullback of a `ν_K`-integrable function along the base projection is
`ν_L`-integrable. -/
theorem integrable_comp_proj_measure {g : AS.Ω → ℝ} (hg : Integrable g AS.v) :
    Integrable[projectiveMeasurableSpace AS L]
      (fun x ↦ g (ParameterSpaceExtension.proj x)) (measure AS L) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  exact (show MeasurePreserving ParameterSpaceExtension.proj (measure AS L) AS.v from
    ⟨measurable_proj_projective AS L, map_measure_proj AS L⟩).integrable_comp_of_integrable hg

/-- Formula (3.21): integrating a pullback from the base against `ν_L` is integrating
against `ν_K`. -/
theorem integral_comp_proj_measure {g : AS.Ω → ℝ} (hg : Integrable g AS.v) :
    ∫ x, g (ParameterSpaceExtension.proj x) ∂measure AS L = ∫ ω, g ω ∂AS.v := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have hm : AEStronglyMeasurable g
      (Measure.map (ParameterSpaceExtension.proj (AS := AS) (L := L)) (measure AS L)) := by
    rw [map_measure_proj AS L]
    exact hg.aestronglyMeasurable
  have h := integral_map (measurable_proj_projective AS L).aemeasurable hm
  rw [map_measure_proj AS L] at h
  exact h.symm

/-- Each finite-stage projection sends the algebraic extension measure to the finite
extension measure. -/
theorem map_measure_projFinite (F : FiniteIntermediateField K L) :
    (let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
    Measure.map (projFinite AS F) (measure AS L) = ParameterSpaceFinExtension.measure AS F) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  ext B hB
  rw [Measure.map_apply (measurable_projFinite_projective AS L F) hB,
    measure_apply AS L (hB.preimage (measurable_projFinite_projective AS L F))]
  change _ = ParameterSpaceExtension.inducedMeasure AS (separableClosure K F.1) B
  rw [ParameterSpaceExtension.inducedMeasure_apply AS (separableClosure K F.1) hB]
  apply lintegral_congr
  intro ω
  let : MeasurableSpace (BaseFiber L ω) := fibreMeasurableSpace L ω
  have hp : Measurable (projFiniteFiber F ω) :=
    Measurable.of_comap_le (le_iSup
      (fun G : FiniteIntermediateField K L ↦
        MeasurableSpace.comap (projFiniteFiber G ω) inferInstance) F)
  have hf : Measurable (fun y : FiniteBaseFiber L F ω ↦ B.indicator (fun _ ↦ (1 : ℝ≥0∞)) y.val) :=
    (measurable_const.indicator hB).comp measurable_subtype_coe
  change (∫⁻ x : BaseFiber L ω,
    B.indicator (fun _ ↦ (1 : ℝ≥0∞)) (projFiniteFiber F ω x).val
    ∂fibreProbabilityMeasure AS L ω) = _
  rw [← lintegral_map hf hp, map_fibreProbabilityMeasure_projFiniteFiber]
  rfl

/-- Pullback from a finite stage preserves integrability. -/
theorem integrable_comp_projFinite_measure (F : FiniteIntermediateField K L)
    {g : ParameterSpaceFinExtension AS F → ℝ}
    (hg : Integrable g (ParameterSpaceFinExtension.measure AS F)) :
    Integrable[projectiveMeasurableSpace AS L] (fun x ↦ g (projFinite AS F x)) (measure AS L) := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  have hg' : Integrable g (Measure.map (projFinite AS F) (measure AS L)) := by
    simpa only [map_measure_projFinite AS L F] using hg
  exact hg'.comp_measurable (measurable_projFinite_projective AS L F)

/-- Integration of an integrable pullback from a finite stage. -/
theorem integral_comp_projFinite_measure (F : FiniteIntermediateField K L)
    {g : ParameterSpaceFinExtension AS F → ℝ}
    (hg : Integrable g (ParameterSpaceFinExtension.measure AS F)) :
    ∫ x, g (projFinite AS F x) ∂measure AS L =
      ∫ y, g y ∂ParameterSpaceFinExtension.measure AS F := by
  let : MeasurableSpace (ParameterSpaceExtension AS L) := projectiveMeasurableSpace AS L
  rw [← map_measure_projFinite AS L F] at hg ⊢
  exact (integral_map (measurable_projFinite_projective AS L F).aemeasurable
    hg.aestronglyMeasurable).symm

/-- Pullback from a finite stage preserves the integral of the norm. -/
theorem integral_norm_comp_projFinite_measure (F : FiniteIntermediateField K L)
    {g : ParameterSpaceFinExtension AS F → ℝ}
    (hg : Integrable g (ParameterSpaceFinExtension.measure AS F)) :
    ∫ x, ‖g (projFinite AS F x)‖ ∂measure AS L =
      ∫ y, ‖g y‖ ∂ParameterSpaceFinExtension.measure AS F :=
  integral_comp_projFinite_measure AS L F hg.norm

end ArakelovGeometry.AdelicStructure.Algebraic

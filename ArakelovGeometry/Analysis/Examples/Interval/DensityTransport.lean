/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Actual cumulative integrals for positive interval densities -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ArakelovGeometry.Analysis.IntervalDensityTransport

variable (f : ℝ → ℝ) (a b : ℝ)

/-- The actual Lebesgue mass of the density on its original interval. -/
def mass : ℝ := ∫ x in a..b, f x

/-- The actual normalized indefinite integral, without changing endpoint values of the density. -/
def cumulative (x : ℝ) : ℝ := (∫ s in a..x, f s) / mass f a b

/-- Strict positivity on the open interval gives strictly positive actual mass,
without requiring endpoint continuity. -/
theorem mass_pos (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x) :
    0 < mass f a b := by
  apply (intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall hfn) hf).mpr
  refine ⟨hab, ?_⟩
  have hs : Ioo a b ⊆ Function.support f ∩ Ioc a b := by
    intro x hx
    exact ⟨ne_of_gt (hfp x hx), hx.1, hx.2.le⟩
  have hv : 0 < volume (Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact hv.trans_le (measure_mono hs)

@[simp]
theorem cumulative_left : cumulative f a b a = 0 := by
  simp [cumulative]

theorem cumulative_right (hA : mass f a b ≠ 0) : cumulative f a b b = 1 := by
  exact div_self hA

/-- Strict increase of the actual indefinite integral follows from positive mass
on every nonempty subinterval. -/
theorem primitive_strictMonoOn (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x) :
    StrictMonoOn (fun x => ∫ s in a..x, f s) (Icc a b) := by
  intro x hx y hy hxy
  have hxu : x ∈ uIcc a b := by simpa only [uIcc_of_le hab.le] using hx
  have hyu : y ∈ uIcc a b := by simpa only [uIcc_of_le hab.le] using hy
  have hau : a ∈ uIcc a b := by simp
  have hax := hf.mono_set (uIcc_subset_uIcc hau hxu)
  have hxyi := hf.mono_set (uIcc_subset_uIcc hxu hyu)
  have hp : 0 < ∫ s in x..y, f s :=
    mass_pos f x y hxy hxyi hfn (fun z hz =>
      hfp z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hax hxyi
  linarith

/-- Normalization by the derived positive mass preserves strict increase. -/
theorem cumulative_strictMonoOn (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x) :
    StrictMonoOn (cumulative f a b) (Icc a b) := by
  intro x hx y hy hxy
  exact (div_lt_div_iff_of_pos_right (mass_pos f a b hab hf hfn hfp)).mpr
    (primitive_strictMonoOn f a b hab hf hfn hfp hx hy hxy)

/-- Actual normalized cumulative integrals are continuous up to the endpoints,
even if the density itself has endpoint jumps. -/
theorem cumulative_continuousOn (hf : IntervalIntegrable f volume a b) :
    ContinuousOn (cumulative f a b) (Icc a b) := by
  have hi : IntegrableOn f (uIcc a b) volume := (intervalIntegrable_iff').mp hf
  have hc := (intervalIntegral.continuousOn_primitive_interval hi).div_const (mass f a b)
  change ContinuousOn (fun x => (∫ s in a..x, f s) / mass f a b) (Icc a b)
  exact hc.mono Icc_subset_uIcc

theorem cumulative_mapsTo (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x) :
    MapsTo (cumulative f a b) (Icc a b) (Icc 0 1) := by
  have hm := (cumulative_strictMonoOn f a b hab hf hfn hfp).monotoneOn
  have hA := (mass_pos f a b hab hf hfn hfp).ne'
  intro x hx
  constructor
  · simpa only [cumulative_left] using hm ⟨le_rfl, hab.le⟩ hx hx.1
  · simpa only [cumulative_right f a b hA] using hm hx ⟨hab.le, le_rfl⟩ hx.2

/-- The actual cumulative range is the full closed unit interval. -/
theorem cumulative_surjOn (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x) :
    SurjOn (cumulative f a b) (Icc a b) (Icc 0 1) := by
  have hA := (mass_pos f a b hab hf hfn hfp).ne'
  intro y hy
  apply intermediate_value_Icc hab.le (cumulative_continuousOn f a b hf)
  simpa only [cumulative_left, cumulative_right f a b hA] using hy

/-- The derivative is obtained from the original density on the actual open interval. -/
theorem cumulative_hasDerivAt (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfc : ContinuousOn f (Ioo a b)) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (cumulative f a b) (f x / mass f a b) x := by
  have hxu : x ∈ uIcc a b := by
    simpa only [uIcc_of_le hab.le] using (show x ∈ Icc a b from ⟨hx.1.le, hx.2.le⟩)
  have hau : a ∈ uIcc a b := by simp
  have hax := hf.mono_set (uIcc_subset_uIcc hau hxu)
  have hc : ContinuousAt f x := hfc.continuousAt (isOpen_Ioo.mem_nhds hx)
  exact (intervalIntegral.integral_hasDerivAt_right hax
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hfc x hx) hc).div_const _

/-- The original cumulative integral as an actual order isomorphism of closed intervals. -/
def cumulativeOrderIso (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x) :
    Icc a b ≃o Icc (0 : ℝ) 1 :=
  StrictMono.orderIsoOfSurjective
    (fun x => ⟨cumulative f a b x, cumulative_mapsTo f a b hab hf hfn hfp x.property⟩)
    (by
      intro x y hxy
      exact cumulative_strictMonoOn f a b hab hf hfn hfp x.property y.property hxy)
    (by
      intro y
      obtain ⟨x, hx, hxy⟩ := cumulative_surjOn f a b hab hf hfn hfp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)

@[simp]
theorem cumulativeOrderIso_apply (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x) (x : Icc a b) :
    (cumulativeOrderIso f a b hab hf hfn hfp x : ℝ) = cumulative f a b x := rfl

/-- The homeomorphism uses the original closed interval subspace topologies. -/
def cumulativeHomeomorph (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x) :
    Icc a b ≃ₜ Icc (0 : ℝ) 1 :=
  (cumulativeOrderIso f a b hab hf hfn hfp).toHomeomorph

@[simp]
theorem cumulativeHomeomorph_apply (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x) (x : Icc a b) :
    (cumulativeHomeomorph f a b hab hf hfn hfp x : ℝ) = cumulative f a b x := rfl

theorem cumulative_deriv (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfc : ContinuousOn f (Ioo a b)) {x : ℝ} (hx : x ∈ Ioo a b) :
    deriv (cumulative f a b) x = f x / mass f a b :=
  (cumulative_hasDerivAt f a b hab hf hfc hx).deriv

/-- The actual cumulative derivative is continuous on the open interval. -/
theorem cumulative_deriv_continuousOn (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfc : ContinuousOn f (Ioo a b)) :
    ContinuousOn (deriv (cumulative f a b)) (Ioo a b) := by
  apply (hfc.div_const (mass f a b)).congr
  intro x hx
  exact cumulative_deriv f a b hab hf hfc hx

theorem cumulative_deriv_pos (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    (hfc : ContinuousOn f (Ioo a b)) {x : ℝ} (hx : x ∈ Ioo a b) :
    0 < deriv (cumulative f a b) x := by
  rw [cumulative_deriv f a b hab hf hfc hx]
  exact div_pos (hfp x hx) (mass_pos f a b hab hf hfn hfp)

/-- The actual normalized cumulative map is continuously differentiable on the open interval. -/
theorem cumulative_contDiffOn (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfc : ContinuousOn f (Ioo a b)) :
    ContDiffOn ℝ 1 (cumulative f a b) (Ioo a b) := by
  apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) isOpen_Ioo).mpr
  refine ⟨?_, by simp, ?_⟩
  · intro x hx
    exact (cumulative_hasDerivAt f a b hab hf hfc hx).differentiableAt.differentiableWithinAt
  · exact contDiffOn_zero.mpr (cumulative_deriv_continuousOn f a b hab hf hfc)

/-- The actual open interval maps onto the actual open unit interval. -/
theorem cumulative_image_Ioo (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x) :
    cumulative f a b '' Ioo a b = Ioo 0 1 := by
  have hm := cumulative_strictMonoOn f a b hab hf hfn hfp
  have hA := (mass_pos f a b hab hf hfn hfp).ne'
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    constructor
    · simpa only [cumulative_left] using
        hm ⟨le_rfl, hab.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
    · simpa only [cumulative_right f a b hA] using
        hm ⟨hx.1.le, hx.2.le⟩ ⟨hab.le, le_rfl⟩ hx.2
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := cumulative_surjOn f a b hab hf hfn hfp ⟨hy.1.le, hy.2.le⟩
    refine ⟨x, ⟨?_, ?_⟩, hxy⟩
    · by_contra h
      have hxa : x = a := le_antisymm (not_lt.mp h) hx.1
      have hy0 : y = 0 := by rw [← hxy, hxa, cumulative_left]
      exact (ne_of_gt hy.1) hy0
    · by_contra h
      have hxb : x = b := le_antisymm hx.2 (not_lt.mp h)
      have hy1 : y = 1 := by rw [← hxy, hxb, cumulative_right f a b hA]
      exact (ne_of_lt hy.2) hy1


/-- The inverse on the original closed interval, extended to a total real function. -/
def inverseCumulative (t : ℝ) : ℝ :=
  Function.invFunOn (cumulative f a b) (Icc a b) t

theorem inverseCumulative_mem (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    {t : ℝ} (ht : t ∈ Icc 0 1) : inverseCumulative f a b t ∈ Icc a b :=
  Function.invFunOn_mem (cumulative_surjOn f a b hab hf hfn hfp ht)

theorem cumulative_inverseCumulative (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    cumulative f a b (inverseCumulative f a b t) = t :=
  Function.invFunOn_eq (cumulative_surjOn f a b hab hf hfn hfp ht)

theorem inverseCumulative_cumulative (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    {x : ℝ} (hx : x ∈ Icc a b) :
    inverseCumulative f a b (cumulative f a b x) = x :=
  (cumulative_strictMonoOn f a b hab hf hfn hfp).injOn.leftInvOn_invFunOn hx

/-- The total inverse agrees with the inverse of the actual cumulative homeomorphism. -/
theorem inverseCumulative_eq_homeomorph_symm (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (t : Icc (0 : ℝ) 1) :
    inverseCumulative f a b t =
      (cumulativeHomeomorph f a b hab hf hfn hfp).symm t := by
  let e := cumulativeHomeomorph f a b hab hf hfn hfp
  have he : cumulative f a b (e.symm t) = t :=
    congrArg Subtype.val (e.apply_symm_apply t)
  have hi := inverseCumulative_cumulative f a b hab hf hfn hfp (e.symm t).property
  rw [he] at hi
  exact hi

theorem inverseCumulative_continuousOn (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) :
    ContinuousOn (inverseCumulative f a b) (Icc 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := continuous_subtype_val.comp
    (cumulativeHomeomorph f a b hab hf hfn hfp).symm.continuous
  apply hc.congr
  intro t
  exact (inverseCumulative_eq_homeomorph_symm f a b hab hf hfn hfp t).symm

theorem inverseCumulative_mapsTo_Ioo (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) :
    MapsTo (inverseCumulative f a b) (Ioo 0 1) (Ioo a b) := by
  intro t ht
  obtain ⟨x, hx, hxt⟩ := (cumulative_image_Ioo f a b hab hf hfn hfp).symm ▸ ht
  rw [← hxt, inverseCumulative_cumulative f a b hab hf hfn hfp ⟨hx.1.le, hx.2.le⟩]
  exact hx


/-- Differentiation of the actual inverse, using its local right-inverse identity. -/
theorem inverseCumulative_hasDerivAt (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo 0 1) :
    HasDerivAt (inverseCumulative f a b)
      (mass f a b / f (inverseCumulative f a b t)) t := by
  have hi := inverseCumulative_mapsTo_Ioo f a b hab hf hfn hfp ht
  have hc := (inverseCumulative_continuousOn f a b hab hf hfn hfp).continuousAt
    (Icc_mem_nhds ht.1 ht.2)
  have hd := cumulative_hasDerivAt f a b hab hf hfc hi
  have hp := div_pos (hfp _ hi) (mass_pos f a b hab hf hfn hfp)
  have he : ∀ᶠ u in nhds t,
      cumulative f a b (inverseCumulative f a b u) = u := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact cumulative_inverseCumulative f a b hab hf hfn hfp ⟨hu.1.le, hu.2.le⟩
  simpa only [inv_div] using HasDerivAt.of_local_left_inverse hc hd hp.ne' he

theorem inverseCumulative_deriv (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo 0 1) :
    deriv (inverseCumulative f a b) t = mass f a b / f (inverseCumulative f a b t) :=
  (inverseCumulative_hasDerivAt f a b hab hf hfn hfp hfc ht).deriv

theorem inverseCumulative_deriv_continuousOn (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b)) :
    ContinuousOn (deriv (inverseCumulative f a b)) (Ioo 0 1) := by
  have hi := inverseCumulative_mapsTo_Ioo f a b hab hf hfn hfp
  have hc := (inverseCumulative_continuousOn f a b hab hf hfn hfp).mono Ioo_subset_Icc_self
  have hden := hfc.comp hc hi
  have hquot : ContinuousOn
      (fun t => mass f a b / f (inverseCumulative f a b t)) (Ioo 0 1) :=
    continuousOn_const.div hden (fun t ht => (hfp _ (hi ht)).ne')
  apply hquot.congr
  intro t ht
  exact inverseCumulative_deriv f a b hab hf hfn hfp hfc ht

theorem inverseCumulative_deriv_pos (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 < deriv (inverseCumulative f a b) t := by
  rw [inverseCumulative_deriv f a b hab hf hfn hfp hfc ht]
  exact div_pos (mass_pos f a b hab hf hfn hfp)
    (hfp _ (inverseCumulative_mapsTo_Ioo f a b hab hf hfn hfp ht))

theorem inverseCumulative_contDiffOn (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b)) :
    ContDiffOn ℝ 1 (inverseCumulative f a b) (Ioo 0 1) := by
  apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) isOpen_Ioo).mpr
  refine ⟨?_, by simp, ?_⟩
  · intro t ht
    have hd := inverseCumulative_hasDerivAt f a b hab hf hfn hfp hfc ht
    exact hd.differentiableAt.differentiableWithinAt
  · exact contDiffOn_zero.mpr
      (inverseCumulative_deriv_continuousOn f a b hab hf hfn hfp hfc)

/-- Strict increase is inherited from the actual cumulative homeomorphism. -/
theorem inverseCumulative_strictMonoOn (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) :
    StrictMonoOn (inverseCumulative f a b) (Icc 0 1) := by
  intro u hu v hv huv
  by_contra h
  have hm := (cumulative_strictMonoOn f a b hab hf hfn hfp).monotoneOn
    (inverseCumulative_mem f a b hab hf hfn hfp hv)
    (inverseCumulative_mem f a b hab hf hfn hfp hu) (not_lt.mp h)
  rw [cumulative_inverseCumulative f a b hab hf hfn hfp hv,
    cumulative_inverseCumulative f a b hab hf hfn hfp hu] at hm
  exact (not_le_of_gt huv) hm

variable (g : ℝ → ℝ) (c d : ℝ)

/-- The actual inverse-cumulative matching function, extended outside its interval. -/
def matchingFunction (x : ℝ) : ℝ :=
  inverseCumulative g c d (cumulative f a b x)

theorem matchingFunction_mapsTo (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    MapsTo (matchingFunction f a b g c d) (Icc a b) (Icc c d) := by
  intro x hx
  exact inverseCumulative_mem g c d hcd hg hgn hgp
    (cumulative_mapsTo f a b hab hf hfn hfp hx)

theorem matchingFunction_mapsTo_Ioo (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    MapsTo (matchingFunction f a b g c d) (Ioo a b) (Ioo c d) := by
  intro x hx
  apply inverseCumulative_mapsTo_Ioo g c d hcd hg hgn hgp
  rw [← cumulative_image_Ioo f a b hab hf hfn hfp]
  exact ⟨x, hx, rfl⟩

theorem matchingFunction_continuousOn (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    ContinuousOn (matchingFunction f a b g c d) (Icc a b) :=
  (inverseCumulative_continuousOn g c d hcd hg hgn hgp).comp
    (cumulative_continuousOn f a b hf) (cumulative_mapsTo f a b hab hf hfn hfp)

theorem cumulative_matchingFunction (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) {x : ℝ} (hx : x ∈ Icc a b) :
    cumulative g c d (matchingFunction f a b g c d x) = cumulative f a b x :=
  cumulative_inverseCumulative g c d hcd hg hgn hgp
    (cumulative_mapsTo f a b hab hf hfn hfp hx)


/-- The matching map as an actual order isomorphism of its original closed intervals. -/
def matchingOrderIso (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    Icc a b ≃o Icc c d :=
  (cumulativeOrderIso f a b hab hf hfn hfp).trans
    (cumulativeOrderIso g c d hcd hg hgn hgp).symm

@[simp]
theorem matchingOrderIso_apply (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x) (x : Icc a b) :
    (matchingOrderIso f a b g c d hab hf hfn hfp hcd hg hgn hgp x : ℝ) =
      matchingFunction f a b g c d x := by
  exact (inverseCumulative_eq_homeomorph_symm g c d hcd hg hgn hgp
    (cumulativeOrderIso f a b hab hf hfn hfp x)).symm

def matchingHomeomorph (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    Icc a b ≃ₜ Icc c d :=
  (matchingOrderIso f a b g c d hab hf hfn hfp hcd hg hgn hgp).toHomeomorph

@[simp]
theorem matchingHomeomorph_apply (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x) (x : Icc a b) :
    (matchingHomeomorph f a b g c d hab hf hfn hfp hcd hg hgn hgp x : ℝ) =
      matchingFunction f a b g c d x :=
  matchingOrderIso_apply f a b g c d hab hf hfn hfp hcd hg hgn hgp x

theorem matchingFunction_left (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    matchingFunction f a b g c d a = c := by
  have hi := inverseCumulative_cumulative g c d hcd hg hgn hgp ⟨le_rfl, hcd.le⟩
  simpa only [matchingFunction, cumulative_left] using hi

theorem matchingFunction_right (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    matchingFunction f a b g c d b = d := by
  have hi := inverseCumulative_cumulative g c d hcd hg hgn hgp ⟨hcd.le, le_rfl⟩
  have hA := (mass_pos f a b hab hf hfn hfp).ne'
  have hB := (mass_pos g c d hcd hg hgn hgp).ne'
  simpa only [matchingFunction, cumulative_right f a b hA, cumulative_right g c d hB]
    using hi

theorem matchingFunction_strictMonoOn (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    StrictMonoOn (matchingFunction f a b g c d) (Icc a b) := by
  intro x hx y hy hxy
  exact inverseCumulative_strictMonoOn g c d hcd hg hgn hgp
    (cumulative_mapsTo f a b hab hf hfn hfp hx)
    (cumulative_mapsTo f a b hab hf hfn hfp hy)
    (cumulative_strictMonoOn f a b hab hf hfn hfp hx hy hxy)

/-- The matching Jacobian is derived from the original densities by the chain rule. -/
theorem matchingFunction_hasDerivAt (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x)
    (hgc : ContinuousOn g (Ioo c d)) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (matchingFunction f a b g c d)
      (f x * mass g c d / (g (matchingFunction f a b g c d x) * mass f a b)) x := by
  have hi : cumulative f a b x ∈ Ioo 0 1 := by
    rw [← cumulative_image_Ioo f a b hab hf hfn hfp]
    exact ⟨x, hx, rfl⟩
  have hd := (inverseCumulative_hasDerivAt g c d hcd hg hgn hgp hgc hi).comp x
    (cumulative_hasDerivAt f a b hab hf hfc hx)
  change HasDerivAt (inverseCumulative g c d ∘ cumulative f a b)
    (f x * mass g c d /
      (g (inverseCumulative g c d (cumulative f a b x)) * mass f a b)) x
  convert hd using 1; ring

theorem matchingFunction_deriv (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    (hfc : ContinuousOn f (Ioo a b)) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) (hgc : ContinuousOn g (Ioo c d))
    {x : ℝ} (hx : x ∈ Ioo a b) :
    deriv (matchingFunction f a b g c d) x =
      f x * mass g c d / (g (matchingFunction f a b g c d x) * mass f a b) :=
  (matchingFunction_hasDerivAt f a b g c d hab hf hfn hfp hfc hcd hg hgn hgp hgc hx).deriv

theorem matchingFunction_deriv_pos (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    (hfc : ContinuousOn f (Ioo a b)) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) (hgc : ContinuousOn g (Ioo c d))
    {x : ℝ} (hx : x ∈ Ioo a b) :
    0 < deriv (matchingFunction f a b g c d) x := by
  rw [matchingFunction_deriv f a b g c d hab hf hfn hfp hfc hcd hg hgn hgp hgc hx]
  exact div_pos (mul_pos (hfp x hx) (mass_pos g c d hcd hg hgn hgp))
    (mul_pos (hgp _ (matchingFunction_mapsTo_Ioo f a b g c d
      hab hf hfn hfp hcd hg hgn hgp hx)) (mass_pos f a b hab hf hfn hfp))

theorem matchingFunction_contDiffOn (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x)
    (hgc : ContinuousOn g (Ioo c d)) :
    ContDiffOn ℝ 1 (matchingFunction f a b g c d) (Ioo a b) := by
  apply (inverseCumulative_contDiffOn g c d hcd hg hgn hgp hgc).comp
    (cumulative_contDiffOn f a b hab hf hfc)
  intro x hx
  rw [← cumulative_image_Ioo f a b hab hf hfn hfp]
  exact ⟨x, hx, rfl⟩



theorem matchingFunction_reverse (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x)
    {x : ℝ} (hx : x ∈ Icc a b) :
    matchingFunction g c d f a b (matchingFunction f a b g c d x) = x := by
  unfold matchingFunction
  rw [cumulative_inverseCumulative g c d hcd hg hgn hgp
    (cumulative_mapsTo f a b hab hf hfn hfp hx)]
  exact inverseCumulative_cumulative f a b hab hf hfn hfp hx

theorem matchingFunction_image_Ioo (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    matchingFunction f a b g c d '' Ioo a b = Ioo c d := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact matchingFunction_mapsTo_Ioo f a b g c d hab hf hfn hfp hcd hg hgn hgp hx
  · intro y hy
    refine ⟨matchingFunction g c d f a b y,
      matchingFunction_mapsTo_Ioo g c d f a b hcd hg hgn hgp hab hf hfn hfp hy, ?_⟩
    exact matchingFunction_reverse g c d f a b hcd hg hgn hgp hab hf hfn hfp
      ⟨hy.1.le, hy.2.le⟩

variable (t : ℝ)

/-- Linear interpolation with the actual matching function. -/
def interpolatedFunction (x : ℝ) : ℝ :=
  (1 - t) * x + t * matchingFunction f a b g c d x

theorem interpolatedFunction_continuousOn (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    ContinuousOn (interpolatedFunction f a b g c d t) (Icc a b) :=
  (continuousOn_id.const_mul (1 - t)).add
    ((matchingFunction_continuousOn f a b g c d hab hf hfn hfp hcd hg hgn hgp).const_mul t)

theorem interpolatedFunction_strictMonoOn (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) (ht : t ∈ Ioo 0 1) :
    StrictMonoOn (interpolatedFunction f a b g c d t) (Icc a b) := by
  intro x hx y hy hxy
  have hm := matchingFunction_strictMonoOn f a b g c d
    hab hf hfn hfp hcd hg hgn hgp hx hy hxy
  dsimp only [interpolatedFunction]
  nlinarith [mul_pos ht.1 (sub_pos.mpr hm), mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hxy)]

theorem interpolatedFunction_left (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    interpolatedFunction f a b g c d t a = (1 - t) * a + t * c := by
  rw [interpolatedFunction, matchingFunction_left f a b g c d hcd hg hgn hgp]

theorem interpolatedFunction_right (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) :
    interpolatedFunction f a b g c d t b = (1 - t) * b + t * d := by
  rw [interpolatedFunction, matchingFunction_right f a b g c d
    hab hf hfn hfp hcd hg hgn hgp]

theorem interpolatedFunction_hasDerivAt (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x)
    (hgc : ContinuousOn g (Ioo c d)) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (interpolatedFunction f a b g c d t)
      (1 - t + t * (f x * mass g c d /
        (g (matchingFunction f a b g c d x) * mass f a b))) x := by
  have hd := matchingFunction_hasDerivAt f a b g c d
    hab hf hfn hfp hfc hcd hg hgn hgp hgc hx
  convert ((hasDerivAt_id x).const_mul (1 - t)).add (hd.const_mul t) using 1 <;>
    first | rfl | simp only [mul_one]

theorem interpolatedFunction_deriv_pos (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x)
    (hgc : ContinuousOn g (Ioo c d)) (ht : t ∈ Ioo 0 1)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    0 < deriv (interpolatedFunction f a b g c d t) x := by
  rw [(interpolatedFunction_hasDerivAt f a b g c d t
    hab hf hfn hfp hfc hcd hg hgn hgp hgc hx).deriv]
  have hp := matchingFunction_deriv_pos f a b g c d
    hab hf hfn hfp hfc hcd hg hgn hgp hgc hx
  rw [matchingFunction_deriv f a b g c d
    hab hf hfn hfp hfc hcd hg hgn hgp hgc hx] at hp
  exact add_pos (sub_pos.mpr ht.2) (mul_pos ht.1 hp)

theorem interpolatedFunction_contDiffOn (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x)
    (hgc : ContinuousOn g (Ioo c d)) :
    ContDiffOn ℝ 1 (interpolatedFunction f a b g c d t) (Ioo a b) :=
  (contDiffOn_id.const_smul (1 - t)).add
    ((matchingFunction_contDiffOn f a b g c d
      hab hf hfn hfp hfc hcd hg hgn hgp hgc).const_smul t)


theorem interpolatedFunction_image_Icc (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) (ht : t ∈ Ioo 0 1) :
    interpolatedFunction f a b g c d t '' Icc a b =
      Icc ((1 - t) * a + t * c) ((1 - t) * b + t * d) := by
  have hl := interpolatedFunction_left f a b g c d t hcd hg hgn hgp
  have hr := interpolatedFunction_right f a b g c d t hab hf hfn hfp hcd hg hgn hgp
  have hm := (interpolatedFunction_strictMonoOn f a b g c d t
    hab hf hfn hfp hcd hg hgn hgp ht).monotoneOn
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    constructor
    · rw [← hl]
      exact hm ⟨le_rfl, hab.le⟩ hx hx.1
    · rw [← hr]
      exact hm hx ⟨hab.le, le_rfl⟩ hx.2
  · intro u hu
    apply intermediate_value_Icc hab.le
      (interpolatedFunction_continuousOn f a b g c d t hab hf hfn hfp hcd hg hgn hgp)
    simpa only [hl, hr] using hu

theorem interpolatedFunction_image_Ioo (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) (ht : t ∈ Ioo 0 1) :
    interpolatedFunction f a b g c d t '' Ioo a b =
      Ioo ((1 - t) * a + t * c) ((1 - t) * b + t * d) := by
  have hl := interpolatedFunction_left f a b g c d t hcd hg hgn hgp
  have hr := interpolatedFunction_right f a b g c d t hab hf hfn hfp hcd hg hgn hgp
  have hm := interpolatedFunction_strictMonoOn f a b g c d t
    hab hf hfn hfp hcd hg hgn hgp ht
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    constructor
    · rw [← hl]
      exact hm ⟨le_rfl, hab.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
    · rw [← hr]
      exact hm ⟨hx.1.le, hx.2.le⟩ ⟨hab.le, le_rfl⟩ hx.2
  · intro u hu
    have huc : u ∈ Icc ((1 - t) * a + t * c) ((1 - t) * b + t * d) :=
      ⟨hu.1.le, hu.2.le⟩
    rw [← interpolatedFunction_image_Icc f a b g c d t
      hab hf hfn hfp hcd hg hgn hgp ht] at huc
    obtain ⟨x, hx, he⟩ := huc
    refine ⟨x, ⟨?_, ?_⟩, he⟩
    · by_contra h
      have hxa : x = a := le_antisymm (not_lt.mp h) hx.1
      have heu : u = (1 - t) * a + t * c := by rw [← he, hxa, hl]
      exact (ne_of_gt hu.1) heu
    · by_contra h
      have hxb : x = b := le_antisymm hx.2 (not_lt.mp h)
      have heu : u = (1 - t) * b + t * d := by rw [← he, hxb, hr]
      exact (ne_of_lt hu.2) heu

/-- The interpolated matching function on the actual closed-interval subspaces. -/
def interpolatedHomeomorph (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hfn : ∀ x, 0 ≤ f x) (hfp : ∀ x ∈ Ioo a b, 0 < f x)
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x) (ht : t ∈ Ioo 0 1) :
    Icc a b ≃ₜ Icc ((1 - t) * a + t * c) ((1 - t) * b + t * d) := by
  have hi := interpolatedFunction_image_Icc f a b g c d t
    hab hf hfn hfp hcd hg hgn hgp ht
  let e : Icc a b ≃o Icc ((1 - t) * a + t * c) ((1 - t) * b + t * d) :=
    StrictMono.orderIsoOfSurjective
    (fun x : Icc a b => ⟨interpolatedFunction f a b g c d t x,
      hi ▸ mem_image_of_mem _ x.property⟩)
    (by
      intro x y hxy
      exact interpolatedFunction_strictMonoOn f a b g c d t
        hab hf hfn hfp hcd hg hgn hgp ht x.property y.property hxy)
    (by
      intro u
      have hu : (u : ℝ) ∈ interpolatedFunction f a b g c d t '' Icc a b := by
        simpa only [hi] using u.property
      obtain ⟨x, hx, he⟩ := hu
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩)
  exact e.toHomeomorph

@[simp]
theorem interpolatedHomeomorph_apply (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hcd : c < d)
    (hg : IntervalIntegrable g volume c d) (hgn : ∀ x, 0 ≤ g x)
    (hgp : ∀ x ∈ Ioo c d, 0 < g x) (ht : t ∈ Ioo 0 1) (x : Icc a b) :
    (interpolatedHomeomorph f a b g c d t hab hf hfn hfp hcd hg hgn hgp ht x : ℝ) =
      interpolatedFunction f a b g c d t x := rfl

/-- Nonnegative substitution with the derived Jacobian on the actual open image interval. -/
theorem lintegral_interpolatedFunction (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x)
    (hgc : ContinuousOn g (Ioo c d)) (ht : t ∈ Ioo 0 1) (H : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioo ((1 - t) * a + t * c) ((1 - t) * b + t * d), H u =
      ∫⁻ x in Ioo a b,
        ENNReal.ofReal (1 - t + t * (f x * mass g c d /
          (g (matchingFunction f a b g c d x) * mass f a b))) *
            H (interpolatedFunction f a b g c d t x) := by
  rw [← interpolatedFunction_image_Ioo f a b g c d t
    hab hf hfn hfp hcd hg hgn hgp ht]
  exact lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioo
    (fun x hx => (interpolatedFunction_hasDerivAt f a b g c d t
      hab hf hfn hfp hfc hcd hg hgn hgp hgc hx).hasDerivWithinAt)
    ((interpolatedFunction_strictMonoOn f a b g c d t
      hab hf hfn hfp hcd hg hgn hgp ht).monotoneOn.mono Ioo_subset_Icc_self) H


/-- Endpoint sets are null, so the same substitution holds on the original closed intervals. -/
theorem lintegral_interpolatedFunction_Icc (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hfn : ∀ x, 0 ≤ f x)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hfc : ContinuousOn f (Ioo a b))
    (hcd : c < d) (hg : IntervalIntegrable g volume c d)
    (hgn : ∀ x, 0 ≤ g x) (hgp : ∀ x ∈ Ioo c d, 0 < g x)
    (hgc : ContinuousOn g (Ioo c d)) (ht : t ∈ Ioo 0 1) (H : ℝ → ℝ≥0∞) :
    ∫⁻ u in Icc ((1 - t) * a + t * c) ((1 - t) * b + t * d), H u =
      ∫⁻ x in Icc a b,
        ENNReal.ofReal (1 - t + t * (f x * mass g c d /
          (g (matchingFunction f a b g c d x) * mass f a b))) *
            H (interpolatedFunction f a b g c d t x) := by
  rw [← setLIntegral_congr Ioo_ae_eq_Icc, ← setLIntegral_congr Ioo_ae_eq_Icc]
  exact lintegral_interpolatedFunction f a b g c d t
    hab hf hfn hfp hfc hcd hg hgn hgp hgc ht H

end ArakelovGeometry.Analysis.IntervalDensityTransport

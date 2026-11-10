/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.Convex.ConvexBodySlices
import ArakelovGeometry.Analysis.Examples.Interval.DensityInequality
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Covering.Besicovitch

/-! # The actual slice step for multiplicative convex volume -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace ArakelovGeometry.ConvexBodySlices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The dimension-zero base, retaining the actual (possibly zero) measure. -/
theorem multiplicative_volume_subsingleton [Subsingleton E] [MeasurableSpace E]
    (μ : Measure E) {t : ℝ} (ht : t ∈ Ioo 0 1) (U V : Set E) :
    ENNReal.ofReal ((μ U).toReal ^ (1 - t) * (μ V).toReal ^ t) ≤
      μ ((1 - t) • U + t • V) := by
  by_cases hU : U.Nonempty
  · by_cases hV : V.Nonempty
    · have hU' : U = univ := eq_univ_iff_forall.mpr fun x =>
        (show hU.choose = x from Subsingleton.elim _ _) ▸ hU.choose_spec
      have hV' : V = univ := eq_univ_iff_forall.mpr fun x =>
        (show hV.choose = x from Subsingleton.elim _ _) ▸ hV.choose_spec
      have hD : (1 - t) • U + t • V = univ := by
        apply eq_univ_iff_forall.mpr
        intro x
        have hz : (0 : E) ∈ U ∧ (0 : E) ∈ V := by simp [hU', hV']
        have hx : x = 0 := Subsingleton.elim _ _
        subst x
        exact ⟨0, ⟨0, hz.1, smul_zero _⟩, 0, ⟨0, hz.2, smul_zero _⟩, zero_add _⟩
      rw [hD, hU', hV', ← Real.rpow_add_of_nonneg ENNReal.toReal_nonneg
        (sub_nonneg.mpr ht.2.le) ht.1.le]
      have he : (1 - t) + t = 1 := by ring
      rw [he, Real.rpow_one]
      exact ENNReal.ofReal_toReal_le
    · rw [not_nonempty_iff_eq_empty.mp hV]
      simp [Real.zero_rpow (ne_of_gt ht.1)]
  · rw [not_nonempty_iff_eq_empty.mp hU]
    simp [Real.zero_rpow (ne_of_gt (sub_pos.mpr ht.2))]

/-- The actual lower-dimensional convex combinations lie in the corresponding
literal section of the original Minkowski combination. -/
theorem convexCombination_slices_subset (A B : Set (ℝ × E)) (x y t : ℝ) :
    (1 - t) • slice A x + t • slice B y ⊆
      slice ((1 - t) • A + t • B) ((1 - t) * x + t * y) := by
  rintro u ⟨v, ⟨v', hv', rfl⟩, w, ⟨w', hw', rfl⟩, rfl⟩
  exact ⟨(1 - t) • (x, v'), ⟨(x, v'), hv', rfl⟩,
    t • (y, w'), ⟨(y, w'), hw', rfl⟩, rfl⟩

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [SecondCountableTopology E] in
/-- The null frontier of an actual compact convex set covers its empty-interior case. -/
theorem measure_eq_zero_of_empty_interior (μ : Measure E) [μ.IsAddHaarMeasure]
    {U : Set E} (hU : IsCompact U) (hcU : Convex ℝ U) (hiU : interior U = ∅) : μ U = 0 := by
  simpa only [frontier, hU.isClosed.closure_eq, hiU, sdiff_empty] using hcU.addHaar_frontier μ

/-- The actual product-body dimension step. The explicit hypothesis is precisely
the same-weight inequality on all compact convex sets of the lower-dimensional
factor; the conclusion is on the original product bodies. -/
theorem multiplicative_volume_prod_step (μ : Measure E) [μ.IsAddHaarMeasure] [SFinite μ]
    {t : ℝ} (ht : t ∈ Ioo 0 1)
    (hIH : ∀ (U V : Set E), IsCompact U → Convex ℝ U → IsCompact V → Convex ℝ V →
      ENNReal.ofReal ((μ U).toReal ^ (1 - t) * (μ V).toReal ^ t) ≤
        μ ((1 - t) • U + t • V))
    {A B : Set (ℝ × E)} (hA : IsCompact A) (hcA : Convex ℝ A)
    (hiA : (interior A).Nonempty) (hB : IsCompact B) (hcB : Convex ℝ B)
    (hiB : (interior B).Nonempty) :
    ENNReal.ofReal (((volume.prod μ) A).toReal ^ (1 - t) *
      ((volume.prod μ) B).toReal ^ t) ≤ (volume.prod μ) ((1 - t) • A + t • B) := by
  let a := sInf (Prod.fst '' A)
  let b := sSup (Prod.fst '' A)
  let c := sInf (Prod.fst '' B)
  let d := sSup (Prod.fst '' B)
  let D := (1 - t) • A + t • B
  have hD : IsCompact D := (hA.smul (1 - t)).add (hB.smul t)
  have hbound := Analysis.IntervalDensityTransport.multiplicative_integral_bound
    (sectionDensity μ A) a b (sectionDensity μ B) c d t
    (projection_lower_lt_upper hA hcA hiA)
    (intervalIntegrable_sectionDensity volume μ hA a b) (sectionDensity_nonneg μ A)
    (fun x hx => sectionDensity_pos_on_Ioo μ hA hcA hiA hx)
    (continuousOn_sectionDensity_Ioo μ hA hcA hiA)
    (projection_lower_lt_upper hB hcB hiB)
    (intervalIntegrable_sectionDensity volume μ hB c d) (sectionDensity_nonneg μ B)
    (fun x hx => sectionDensity_pos_on_Ioo μ hB hcB hiB hx)
    (continuousOn_sectionDensity_Ioo μ hB hcB hiB) ht (sectionVolume μ D)
    (fun x _ y _ =>
      (hIH (slice A x) (slice B y) (isCompact_slice hA x) (convex_slice hcA x)
        (isCompact_slice hB y) (convex_slice hcB y)).trans
          (measure_mono (convexCombination_slices_subset A B x y t)))
  have hmA : Analysis.IntervalDensityTransport.mass (sectionDensity μ A) a b =
      ((volume.prod μ) A).toReal :=
    intervalIntegral_sectionDensity volume μ hA hcA (hiA.mono interior_subset)
  have hmB : Analysis.IntervalDensityTransport.mass (sectionDensity μ B) c d =
      ((volume.prod μ) B).toReal :=
    intervalIntegral_sectionDensity volume μ hB hcB (hiB.mono interior_subset)
  rw [hmA, hmB] at hbound
  apply hbound.trans
  calc
    _ ≤ ∫⁻ x in (univ : Set ℝ), sectionVolume μ D x := lintegral_mono_set (subset_univ _)
    _ = _ := by simpa only [setLIntegral_univ] using lintegral_sectionVolume volume μ hD

/-- The actual product dimension step including all zero-volume branches. -/
theorem multiplicative_volume_prod (μ : Measure E) [μ.IsAddHaarMeasure] [SFinite μ]
    {t : ℝ} (ht : t ∈ Ioo 0 1)
    (hIH : ∀ (U V : Set E), IsCompact U → Convex ℝ U → IsCompact V → Convex ℝ V →
      ENNReal.ofReal ((μ U).toReal ^ (1 - t) * (μ V).toReal ^ t) ≤
        μ ((1 - t) • U + t • V))
    {A B : Set (ℝ × E)} (hA : IsCompact A) (hcA : Convex ℝ A)
    (hB : IsCompact B) (hcB : Convex ℝ B) :
    ENNReal.ofReal (((volume.prod μ) A).toReal ^ (1 - t) *
      ((volume.prod μ) B).toReal ^ t) ≤ (volume.prod μ) ((1 - t) • A + t • B) := by
  by_cases hiA : (interior A).Nonempty
  · by_cases hiB : (interior B).Nonempty
    · exact multiplicative_volume_prod_step μ ht hIH hA hcA hiA hB hcB hiB
    · have hz := measure_eq_zero_of_empty_interior (volume.prod μ) hB hcB
        (not_nonempty_iff_eq_empty.mp hiB)
      simp [hz, Real.zero_rpow (ne_of_gt ht.1)]
  · have hz := measure_eq_zero_of_empty_interior (volume.prod μ) hA hcA
      (not_nonempty_iff_eq_empty.mp hiA)
    simp [hz, Real.zero_rpow (ne_of_gt (sub_pos.mpr ht.2))]

end ArakelovGeometry.ConvexBodySlices

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.GeometryOfNumbers.ConvexVolumeInduction
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Multiplicative convex volume in the original finite real coordinate spaces -/

noncomputable section
namespace ArakelovGeometry.ConvexVolume

open MeasureTheory Set
open scoped ENNReal Pointwise

/-- Split the first coordinate by the canonical finite-coordinate measurable equivalence. -/
def coordinateSplit (n : ℕ) : (Fin (n + 1) → ℝ) ≃L[ℝ] ℝ × (Fin n → ℝ) :=
  ({ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).toEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } :
    (Fin (n + 1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin n → ℝ)).toContinuousLinearEquiv

/-- This splitting preserves the original product Lebesgue measure, with no scaling factor. -/
theorem measurePreserving_coordinateSplit (n : ℕ) :
    MeasurePreserving (coordinateSplit n) volume (volume.prod volume) :=
  volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0

/-- Compact original sets and their actual coordinate images have identical volume. -/
theorem volume_coordinateSplit_image (n : ℕ) {S : Set (Fin (n + 1) → ℝ)} (hS : IsCompact S) :
    (volume.prod volume) (coordinateSplit n '' S) = volume S := by
  have h := (measurePreserving_coordinateSplit n).measure_preimage
    (hS.image (coordinateSplit n).continuous).measurableSet.nullMeasurableSet
  simpa only [Set.preimage_image_eq _ (coordinateSplit n).injective] using h.symm

/-- The actual coordinate split takes the original Minkowski combination to the product one. -/
theorem coordinateSplit_image_combination (n : ℕ) (A B : Set (Fin (n + 1) → ℝ)) (t : ℝ) :
    coordinateSplit n '' ((1 - t) • A + t • B) =
      (1 - t) • (coordinateSplit n '' A) + t • (coordinateSplit n '' B) := by
  ext p
  constructor
  · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(1 - t) • coordinateSplit n a, ⟨coordinateSplit n a, ⟨a, ha, rfl⟩, rfl⟩,
      t • coordinateSplit n b, ⟨coordinateSplit n b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
    simp only [map_add, map_smul]
  · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, _, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(1 - t) • a + t • b, ⟨(1 - t) • a, ⟨a, ha, rfl⟩,
      t • b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
    simp only [map_add, map_smul]

/-- The multiplicative convex-volume inequality on the original finite real coordinate spaces. -/
theorem multiplicative_volume_fin (n : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    ∀ (A B : Set (Fin n → ℝ)), IsCompact A → Convex ℝ A → IsCompact B → Convex ℝ B →
      ENNReal.ofReal ((volume A).toReal ^ (1 - t) * (volume B).toReal ^ t) ≤
        volume ((1 - t) • A + t • B) := by
  induction n with
  | zero =>
      intro A B _ _ _ _
      exact ConvexBodySlices.multiplicative_volume_subsingleton volume ht A B
  | succ n ih =>
      intro A B hA hcA hB hcB
      have h := ConvexBodySlices.multiplicative_volume_prod volume ht ih
        (hA.image (coordinateSplit n).continuous) (hcA.linear_image (coordinateSplit n).toLinearMap)
        (hB.image (coordinateSplit n).continuous) (hcB.linear_image (coordinateSplit n).toLinearMap)
      rw [← coordinateSplit_image_combination n A B t] at h
      rw [volume_coordinateSplit_image n hA, volume_coordinateSplit_image n hB,
        volume_coordinateSplit_image n ((hA.smul (1 - t)).add (hB.smul t))] at h
      exact h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The multiplicative convex-volume inequality for the actual Haar measure on any finite space. -/
theorem multiplicative_volume (μ : Measure E) [μ.IsAddHaarMeasure]
    {t : ℝ} (ht : t ∈ Ioo 0 1) {A B : Set E}
    (hA : IsCompact A) (hcA : Convex ℝ A) (hB : IsCompact B) (hcB : Convex ℝ B) :
    ENNReal.ofReal ((μ A).toReal ^ (1 - t) * (μ B).toReal ^ t) ≤
      μ ((1 - t) • A + t • B) := by
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  let ν : Measure (Fin n → ℝ) := Measure.map e μ
  let c := ν.addHaarScalarFactor volume
  have hc : (0 : ℝ) < c := NNReal.coe_pos.mpr
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume)
  have hmeasure (S : Set E) (hS : IsCompact S) :
      μ S = (c : ℝ≥0∞) * volume (e '' S) := by
    have hm : ν (e '' S) = μ S := by
      change (Measure.map e μ) (e '' S) = μ S
      rw [Measure.map_apply e.continuous.measurable (hS.image e.continuous).measurableSet]
      rw [Set.preimage_image_eq _ e.injective]
    rw [← hm, Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure ν volume
      (hS.image e.continuous).closure]
    rfl
  have hD : IsCompact ((1 - t) • A + t • B) := (hA.smul (1 - t)).add (hB.smul t)
  have hDA : IsCompact (e '' ((1 - t) • A + t • B)) := hD.image e.continuous
  have himage : e '' ((1 - t) • A + t • B) = (1 - t) • (e '' A) + t • (e '' B) := by
    rw [Set.image_add, image_smul_set, image_smul_set]
  have hfin := multiplicative_volume_fin n ht (e '' A) (e '' B)
    (hA.image e.continuous) (hcA.linear_image e.toLinearMap)
    (hB.image e.continuous) (hcB.linear_image e.toLinearMap)
  rw [← himage] at hfin
  have hfinReal := (ENNReal.ofReal_le_iff_le_toReal hDA.measure_lt_top.ne).mp hfin
  apply (ENNReal.ofReal_le_iff_le_toReal hD.measure_lt_top.ne).mpr
  rw [hmeasure A hA, hmeasure B hB, hmeasure _ hD]
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal]
  calc
    ((c : ℝ) * (volume (e '' A)).toReal) ^ (1 - t) *
        ((c : ℝ) * (volume (e '' B)).toReal) ^ t =
        (c : ℝ) * ((volume (e '' A)).toReal ^ (1 - t) * (volume (e '' B)).toReal ^ t) := by
      rw [Real.mul_rpow hc.le ENNReal.toReal_nonneg,
        Real.mul_rpow hc.le ENNReal.toReal_nonneg]
      have hp : (c : ℝ) ^ (1 - t) * (c : ℝ) ^ t = c := by
        rw [← Real.rpow_add hc, sub_add_cancel, Real.rpow_one]
      calc
        _ = ((c : ℝ) ^ (1 - t) * (c : ℝ) ^ t) *
          ((volume (e '' A)).toReal ^ (1 - t) * (volume (e '' B)).toReal ^ t) := by ring
        _ = _ := by rw [hp]
    _ ≤ (c : ℝ) * (volume (e '' ((1 - t) • A + t • B))).toReal :=
      mul_le_mul_of_nonneg_left hfinReal hc.le

/-- Symmetrization by the actual half-difference body does not decrease Haar volume. -/
theorem measure_le_half_difference (μ : Measure E) [μ.IsAddHaarMeasure]
    {A : Set E} (hA : IsCompact A) (hcA : Convex ℝ A) :
    μ A ≤ μ ((1 / 2 : ℝ) • (A + -A)) := by
  have h := multiplicative_volume μ (t := (1 / 2 : ℝ)) (by norm_num)
    hA hcA hA.neg hcA.neg
  have hhalf : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [hhalf, μ.measure_neg] at h
  have hp : (μ A).toReal ^ (1 / 2 : ℝ) * (μ A).toReal ^ (1 / 2 : ℝ) = (μ A).toReal := by
    rw [← Real.rpow_add' ENNReal.toReal_nonneg (by norm_num : (1 / 2 : ℝ) + 1 / 2 ≠ 0)]
    norm_num
  rw [hp, ENNReal.ofReal_toReal hA.measure_lt_top.ne] at h
  simpa only [smul_add] using h

end ArakelovGeometry.ConvexVolume

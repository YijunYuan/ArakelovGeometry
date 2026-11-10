/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Actual ordinary Euclidean product measure under scalar block regrouping -/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.EuclideanProductMeasure

open MeasureTheory MeasureTheory.Measure TopologicalSpace.PositiveCompacts

variable {ι : Type*} [Fintype ι] (κ : ι → Type*) [∀ j, Fintype (κ j)]

/-- The literal scalar-coordinate flattening, as a continuous linear equivalence. -/
def flatten : (∀ j, κ j → ℝ) ≃L[ℝ] ((Σ j, κ j) → ℝ) :=
  (LinearEquiv.piCurry ℝ (fun j (_ : κ j) => ℝ)).symm.toContinuousLinearEquiv

/-- Scalar block regrouping preserves the actual product Lebesgue measure. -/
theorem flatten_measurePreserving : MeasurePreserving (flatten κ) volume volume := by
  classical
  refine ⟨(flatten κ).continuous.measurable, ?_⟩
  let μ : Measure ((Σ j, κ j) → ℝ) := volume.map (flatten κ)
  let : IsAddHaarMeasure μ := by
    change IsAddHaarMeasure (volume.map (flatten κ))
    infer_instance
  have hm : μ (piIcc01 (Σ j, κ j)) = 1 := by
    rw [Measure.map_apply (flatten κ).continuous.measurable (piIcc01 _).isCompact.measurableSet]
    simp only [piIcc01, TopologicalSpace.PositiveCompacts.coe_mk,
      TopologicalSpace.Compacts.coe_mk]
    have he : (flatten κ) ⁻¹' Set.pi Set.univ
        (fun _ : Σ j, κ j => Set.Icc (0 : ℝ) 1) =
        Set.pi Set.univ (fun j => Set.pi Set.univ (fun _ : κ j => Set.Icc (0 : ℝ) 1)) := by
      ext x
      simp [flatten, Pi.le_def, Sigma.forall, Sigma.uncurry]
    rw [he, volume_pi_pi]
    simp_rw [volume_pi_pi, Real.volume_Icc]
    norm_num
  have h := addHaarMeasure_unique μ (piIcc01 (Σ j, κ j))
  rw [hm, one_smul, addHaarMeasure_eq_volume_pi] at h
  exact h

/-- Ordinary Euclidean blocks obtained by regrouping the original scalar coordinates. -/
def blockCoordinates : ((Σ j, κ j) → ℝ) ≃ₗ[ℝ] (∀ j, EuclideanSpace ℝ (κ j)) :=
  (flatten κ).symm.toLinearEquiv.trans
    (LinearEquiv.piCongrRight fun j => (WithLp.linearEquiv 2 ℝ (κ j → ℝ)).symm)

/-- Actual scalar regrouping followed by the native Euclidean wrappers preserves volume. -/
theorem blockCoordinates_measurePreserving :
    MeasurePreserving (blockCoordinates κ) volume volume := by
  have hi : MeasurePreserving (flatten κ).symm volume volume :=
    (show MeasurePreserving ((flatten κ).toHomeomorph.toMeasurableEquiv) volume volume
      from flatten_measurePreserving κ).symm
  exact (volume_preserving_pi fun j => PiLp.volume_preserving_toLp (κ j)).comp hi

end ArakelovGeometry.EuclideanProductMeasure

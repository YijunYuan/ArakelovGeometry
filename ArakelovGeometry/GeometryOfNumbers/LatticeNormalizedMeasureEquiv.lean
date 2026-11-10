/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.GeometryOfNumbers.LatticeNormalizedMeasure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Actual normalized lattice measure under actual linear coordinates -/

noncomputable section
open Module MeasureTheory MeasureTheory.Measure Set

namespace ArakelovGeometry.GeometryOfNumbers

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (e : F ≃L[ℝ] E) (μ : Measure E) [IsAddHaarMeasure μ]
  (ν : Measure F) [IsAddHaarMeasure ν]

/-- Actual normalized lattice measure is preserved by the actual lattice pullback coordinates. -/
theorem map_latticeNormalizedMeasure_comap :
    Measure.map e (latticeNormalizedMeasure (ZLattice.comap ℝ L e.toLinearMap) ν) =
      latticeNormalizedMeasure L μ := by
  let ν₀ : Measure F := μ.map e.symm
  let : IsAddHaarMeasure ν₀ := e.symm.isAddHaarMeasure_map μ
  have he : MeasurePreserving e ν₀ μ := by
    refine ⟨e.continuous.measurable, ?_⟩
    dsimp only [ν₀]
    rw [Measure.map_map e.continuous.measurable e.symm.continuous.measurable,
      show (e ∘ e.symm : E → E) = id from funext e.apply_symm_apply, Measure.map_id]
  have hcReal := ZLattice.covolume_comap L μ ν₀ he
  have hc : addCovolume (ZLattice.comap ℝ L e.toLinearMap) F ν₀ = addCovolume L E μ :=
    (ENNReal.toReal_eq_toReal_iff'
      (latticeCovolume_pos_lt_top (ZLattice.comap ℝ L e.toLinearMap) ν₀).2.ne
      (latticeCovolume_pos_lt_top L μ).2.ne).mp hcReal
  rw [latticeNormalizedMeasure_eq (ZLattice.comap ℝ L e.toLinearMap) ν ν₀,
    latticeNormalizedMeasure, Measure.map_smul, hc, he.map_eq]
  rfl

/-- The actual coordinate map is measure preserving for the two derived normalized measures. -/
theorem measurePreserving_latticeNormalizedMeasure_comap :
    MeasurePreserving e (latticeNormalizedMeasure (ZLattice.comap ℝ L e.toLinearMap) ν)
      (latticeNormalizedMeasure L μ) :=
  ⟨e.continuous.measurable, map_latticeNormalizedMeasure_comap L e μ ν⟩

/-- An actual measurable set has exactly its actual coordinate-preimage normalized measure. -/
theorem latticeNormalizedMeasure_comap_preimage {S : Set E} (hS : MeasurableSet S) :
    latticeNormalizedMeasure (ZLattice.comap ℝ L e.toLinearMap) ν (e ⁻¹' S) =
      latticeNormalizedMeasure L μ S := by
  have h := congrArg (fun τ : Measure E => τ S) (map_latticeNormalizedMeasure_comap L e μ ν)
  rw [Measure.map_apply e.continuous.measurable hS] at h
  exact h

end ArakelovGeometry.GeometryOfNumbers

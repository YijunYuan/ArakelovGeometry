/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.Measure.IntegralDualCovolume
public import ArakelovGeometry.GeometryOfNumbers.Measure.LatticeNormalizedMeasure

/-! # Integral-dual normalized measure and primal Euclidean covolume -/

@[expose] public section

noncomputable section
open MeasureTheory

namespace ArakelovGeometry.GeometryOfNumbers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

local instance : MeasureSpace E := measureSpaceOfInnerProductSpace
attribute [local instance] strongDualInnerProduct

/-- Normalizing canonical dual volume by the actual integral dual multiplies it by
the canonical primal covolume. The actual reciprocal-covolume theorem supplies the factor. -/
theorem latticeNormalizedMeasure_integralDual_eq_smul_volume :
    letI : MeasurableSpace (StrongDual ℝ E) := borel _
    letI : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace (E := StrongDual ℝ E)
    latticeNormalizedMeasure (integralDual L) volume =
      ENNReal.ofReal (ZLattice.covolume L volume) • (volume : Measure (StrongDual ℝ E)) := by
  let : MeasurableSpace (StrongDual ℝ E) := borel _
  let : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := StrongDual ℝ E)
  let := integralDual_discrete L
  let := integralDual_isZLattice L
  have hd : addCovolume (integralDual L) (StrongDual ℝ E) volume =
      ENNReal.ofReal (ZLattice.covolume (integralDual L) volume) :=
    (ENNReal.ofReal_toReal (latticeCovolume_pos_lt_top (integralDual L) volume).2.ne).symm
  rw [latticeNormalizedMeasure, hd, integralDual_covolume L,
    ENNReal.ofReal_inv_of_pos (ZLattice.covolume_pos L volume), inv_inv]

/-- Exact normalized measure of any actual dual set, with no measurability assumption. -/
theorem latticeNormalizedMeasure_integralDual_apply (B : Set (StrongDual ℝ E)) :
    letI : MeasurableSpace (StrongDual ℝ E) := borel _
    letI : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace (E := StrongDual ℝ E)
    latticeNormalizedMeasure (integralDual L) volume B =
      ENNReal.ofReal (ZLattice.covolume L volume) * volume B := by
  let : MeasurableSpace (StrongDual ℝ E) := borel _
  let : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := StrongDual ℝ E)
  rw [latticeNormalizedMeasure_integralDual_eq_smul_volume L,
    Measure.smul_apply, smul_eq_mul]

end ArakelovGeometry.GeometryOfNumbers

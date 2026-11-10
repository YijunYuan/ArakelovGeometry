/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.Lattice.LatticeSubspaceCoordinates
import ArakelovGeometry.GeometryOfNumbers.Convex.ConvexIntegerCount
import ArakelovGeometry.GeometryOfNumbers.Convex.ConvexVolume
import ArakelovGeometry.GeometryOfNumbers.Measure.PrimitiveLineMeasure
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-! # Actual affine scalar sections and their primitive lattice counts -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.PrimitiveAffineSections

open MeasureTheory Set
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The literal real preimage of the original body under an actual affine line. -/
def affineSection (C : Set E) (v z : E) : Set ℝ :=
  (fun t : ℝ => t • v + z) ⁻¹' C

/-- A nonzero affine scalar line is a closed embedding, so its actual sections are compact. -/
theorem isCompact_affineSection {C : Set E} (hC : IsCompact C) {v : E} (hv : v ≠ 0)
    (z : E) : IsCompact (affineSection C v z) :=
  ((Homeomorph.addRight z).isClosedEmbedding.comp
    (isClosedEmbedding_smul_left (𝕜 := ℝ) hv)).isCompact_preimage hC

/-- Literal scalar affine sections of a convex set are convex. -/
theorem convex_affineSection {C : Set E} (hC : Convex ℝ C) (v z : E) :
    Convex ℝ (affineSection C v z) :=
  Convex.affine_preimage ((LinearMap.toSpanSingleton ℝ E v).toAffineMap +
    AffineMap.const ℝ ℝ z) hC

/-- The half-difference of an actual affine section lies in the actual central section. -/
theorem half_difference_affineSection_subset_central {C : Set E} (hC : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (v z : E) :
    (1 / 2 : ℝ) • (affineSection C v z + -affineSection C v z) ⊆
      affineSection C v 0 := by
  rintro _ ⟨_, ⟨s, hs, t, ht, rfl⟩, rfl⟩
  have ht' : -t ∈ affineSection C v z := by simpa using ht
  have h := hC hs (hsymm _ ht') (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
  change ((1 / 2 : ℝ) * (s + t)) • v + 0 ∈ C
  convert h using 1
  module

/-- The actual affine section's Lebesgue measure is at most the central section's measure. -/
theorem volume_affineSection_le_central {C : Set E} (hcompact : IsCompact C)
    (hconvex : Convex ℝ C) (hsymm : ∀ x ∈ C, -x ∈ C) {v : E} (hv : v ≠ 0) (z : E) :
    volume (affineSection C v z) ≤ volume (affineSection C v 0) :=
  (ConvexVolume.measure_le_half_difference volume (isCompact_affineSection hcompact hv z)
    (convex_affineSection hconvex v z)).trans
      (measure_mono (half_difference_affineSection_subset_central hconvex hsymm v z))

/-- Both actual primitive endpoints make the real central-coordinate length at least two. -/
theorem two_le_volume_central {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) {v : E} (hv : v ≠ 0) (hvC : v ∈ C) :
    2 ≤ (volume (affineSection C v 0)).toReal := by
  have hneg : (-1 : ℝ) ∈ affineSection C v 0 := by
    simpa [affineSection] using hsymm v hvC
  have hpos : (1 : ℝ) ∈ affineSection C v 0 := by simpa [affineSection] using hvC
  have hsub : Icc (-1 : ℝ) 1 ⊆ affineSection C v 0 :=
    (convex_affineSection hconvex v 0).ordConnected.out hneg hpos
  have h := ENNReal.toReal_mono (isCompact_affineSection hcompact hv 0).measure_lt_top.ne
    (measure_mono (μ := volume) hsub)
  norm_num [Real.volume_Icc] at h
  exact h

/-- Actual scalar integer fibres have the precise factor used in the lattice-count induction. -/
theorem natCard_affine_integer_le_three_halves_central {C : Set E} (hcompact : IsCompact C)
    (hconvex : Convex ℝ C) (hsymm : ∀ x ∈ C, -x ∈ C) {v : E} (hv : v ≠ 0)
    (hvC : v ∈ C) (z : E) :
    (Nat.card {n : ℤ // (n : ℝ) • v + z ∈ C} : ℝ) ≤
      (3 / 2 : ℝ) * (volume (affineSection C v 0)).toReal := by
  have hlen := ENNReal.toReal_mono (isCompact_affineSection hcompact hv 0).measure_lt_top.ne
    (volume_affineSection_le_central hcompact hconvex hsymm hv z)
  exact ConvexIntegerCount.natCard_integer_points_le_three_halves_mul
    (isCompact_affineSection hcompact hv z) (convex_affineSection hconvex v z) hlen
    (two_le_volume_central hcompact hconvex hsymm hv hvC)

section Lattice

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (v : L) (hv : (v : E) ≠ 0)
  [MeasurableSpace (ℝ ∙ (v : E))] [BorelSpace (ℝ ∙ (v : E))]
  (ν : Measure (ℝ ∙ (v : E))) [ν.IsAddHaarMeasure]

include hv in
/-- The integer-fibre bound uses the actual intersection lattice normalization. -/
theorem natCard_affine_integer_le_three_halves_normalized
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E))
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hvC : (v : E) ∈ C) (z : E) :
    (Nat.card {n : ℤ // (n : ℝ) • (v : E) + z ∈ C} : ℝ) ≤
      (3 / 2 : ℝ) * (latticeNormalizedMeasure
        (LatticeSubspaceCoordinates.intersectionAsSubmodule L (ℝ ∙ (v : E))) ν
          ((ℝ ∙ (v : E)).subtype ⁻¹' C)).toReal := by
  rw [PrimitiveLineMeasure.latticeNormalizedMeasure_section_eq_volume_preimage
    L v hv ν hprimitive hcompact.isClosed.measurableSet]
  simpa only [affineSection, add_zero] using
    natCard_affine_integer_le_three_halves_central hcompact hconvex hsymm hv hvC z

end Lattice

end ArakelovGeometry.GeometryOfNumbers.PrimitiveAffineSections

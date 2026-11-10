/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.ConvexCentralSection
public import ArakelovGeometry.GeometryOfNumbers.LatticeSubspaceCoordinates

/-! # Actual normalized lattice central sections and quotient projections -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.LatticeCentralSection

open MeasureTheory Set
open ConvexCentralSection LatticeSubspaceCoordinates LatticeSubspaceQuotient LatticeSubspaceBasis
open scoped ENNReal

attribute [local instance] Submodule.closed_of_finiteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (U : Submodule ℝ E)
  (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U)

/-- The actual coordinate section is the literal preimage under the constructed affine fibre. -/
theorem sectionAt_symm_image_eq_preimage (C : Set E) (q : E ⧸ U) :
    sectionAt ((adaptedCoordinates L U hU).symm '' C) q =
      (fun u : U => adaptedCoordinates L U hU (u, q)) ⁻¹' C := by
  let e := adaptedCoordinates L U hU
  ext u
  change (u, q) ∈ e.symm '' C ↔ e (u, q) ∈ C
  constructor
  · rintro ⟨x, hx, hEq⟩
    have h : e (u, q) = x := by rw [← hEq, e.apply_symm_apply]
    exact h.symm ▸ hx
  · intro hu
    exact ⟨e (u, q), hu, e.symm_apply_apply (u, q)⟩

/-- The zero section of the actual coordinate body is the actual subspace preimage of C. -/
theorem central_section_eq_subtype_preimage (C : Set E) :
    sectionAt ((adaptedCoordinates L U hU).symm '' C) 0 = U.subtype ⁻¹' C := by
  rw [sectionAt_symm_image_eq_preimage L U hU]
  ext u
  change adaptedCoordinates L U hU (u, 0) ∈ C ↔ (u : E) ∈ C
  rw [adaptedCoordinates_inl]

omit [FiniteDimensional ℝ E] in
/-- Inclusion identifies the literal subspace preimage with the actual intersection C ∩ U. -/
theorem subtype_image_preimage_eq_intersection (C : Set E) :
    U.subtype '' (U.subtype ⁻¹' C) = C ∩ (U : Set E) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hu, u.property⟩
  · rintro ⟨hxC, hxU⟩
    exact ⟨⟨x, hxU⟩, hxC, rfl⟩

/-- The actual second-coordinate projection is exactly the actual quotient image of C. -/
theorem projection_symm_image_eq_quotient_image (C : Set E) :
    Prod.snd '' ((adaptedCoordinates L U hU).symm '' C) = U.mkQ '' C := by
  let e := adaptedCoordinates L U hU
  have hsnd : (fun x : E => (e.symm x).2) = U.mkQ := by
    funext x
    have h := quotient_adaptedCoordinates L U hU (e.symm x)
    rw [e.apply_symm_apply] at h
    exact h.symm
  rw [Set.image_image]
  exact congrArg (fun f : E → E ⧸ U => f '' C) hsnd

section Measure

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace (E ⧸ U)] [BorelSpace (E ⧸ U)]

/-- The inverse coordinate orientation needed by the original-body comparison is produced
from the actual normalized adapted-coordinate theorem. -/
theorem measurePreserving_adaptedCoordinates_symm_normalizedMeasure
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure U) [ν.IsAddHaarMeasure]
    (ξ : Measure (E ⧸ U)) [ξ.IsAddHaarMeasure] :
    MeasurePreserving (adaptedCoordinates L U hU).symm (latticeNormalizedMeasure L μ)
      ((latticeNormalizedMeasure (intersectionAsSubmodule L U) ν).prod
        (latticeNormalizedMeasure (quotientImage L U) ξ)) := by
  exact MeasurePreserving.symm
    (adaptedCoordinates L U hU).toHomeomorph.toMeasurableEquiv
    (measurePreserving_adaptedCoordinates_normalizedMeasure L U hU μ ν ξ)

omit [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (E ⧸ U)] [BorelSpace (E ⧸ U)] in
/-- Actual affine fibres are bounded by the actual subspace section with its actual
intersection-lattice normalized Haar measure. -/
theorem latticeNormalizedMeasure_section_le_central
    (ν : Measure U) [ν.IsAddHaarMeasure]
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ z ∈ C, -z ∈ C) (q : E ⧸ U) :
    latticeNormalizedMeasure (intersectionAsSubmodule L U) ν
        ((fun u : U => adaptedCoordinates L U hU (u, q)) ⁻¹' C) ≤
      latticeNormalizedMeasure (intersectionAsSubmodule L U) ν (U.subtype ⁻¹' C) := by
  let := intersectionAsSubmodule_discrete L U hU
  let := intersectionAsSubmodule_isZLattice L U hU
  let := latticeNormalizedMeasure_isAddHaar (intersectionAsSubmodule L U) ν
  let e := adaptedCoordinates L U hU
  have hsymmI : ∀ z ∈ e.symm '' C, -z ∈ e.symm '' C := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, hsymm x hx, map_neg e.symm x⟩
  have h := measure_sectionAt_le_central
    (latticeNormalizedMeasure (intersectionAsSubmodule L U) ν)
    (hcompact.image e.symm.continuous) (hconvex.linear_image e.symm.toLinearMap) hsymmI q
  simpa only [e, central_section_eq_subtype_preimage L U hU,
    sectionAt_symm_image_eq_preimage L U hU] using h

include hU in
/-- The original lattice-normalized body volume is bounded by the literal intersection
section and actual quotient image, normalized by their actual lattices. -/
theorem latticeNormalizedMeasure_le_intersection_mul_quotient
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure U) [ν.IsAddHaarMeasure]
    (ξ : Measure (E ⧸ U)) [ξ.IsAddHaarMeasure]
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ z ∈ C, -z ∈ C) :
    latticeNormalizedMeasure L μ C ≤
      latticeNormalizedMeasure (intersectionAsSubmodule L U) ν (U.subtype ⁻¹' C) *
        latticeNormalizedMeasure (quotientImage L U) ξ (U.mkQ '' C) := by
  let := intersectionAsSubmodule_discrete L U hU
  let := intersectionAsSubmodule_isZLattice L U hU
  let := quotientImage_discrete L U hU
  let := quotientImage_isZLattice L U hU
  let := latticeNormalizedMeasure_isAddHaar (intersectionAsSubmodule L U) ν
  let := latticeNormalizedMeasure_isAddHaar (quotientImage L U) ξ
  have h := measure_le_central_mul_projection_of_measurePreserving
    (adaptedCoordinates L U hU).symm (latticeNormalizedMeasure L μ)
    (latticeNormalizedMeasure (intersectionAsSubmodule L U) ν)
    (latticeNormalizedMeasure (quotientImage L U) ξ)
    (measurePreserving_adaptedCoordinates_symm_normalizedMeasure L U hU μ ν ξ)
    hcompact hconvex hsymm
  simpa only [central_section_eq_subtype_preimage L U hU,
    projection_symm_image_eq_quotient_image L U hU] using h

end Measure

end ArakelovGeometry.GeometryOfNumbers.LatticeCentralSection

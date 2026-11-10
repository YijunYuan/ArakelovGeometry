/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.GeometryOfNumbers.LatticeCentralSection
import ArakelovGeometry.GeometryOfNumbers.LatticeIntegralDualCoordinates
import ArakelovGeometry.GeometryOfNumbers.PolarSectionProjection
import ArakelovGeometry.GeometryOfNumbers.PrimitiveLineDualMeasure

/-! # Actual normalized dual volumes of lattice sections and quotient images -/

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.LatticeDualCentralSection

open Module MeasureTheory Set
open LatticeSubspaceBasis LatticeSubspaceCoordinates LatticeSubspaceQuotient
open LatticeIntegralDualCoordinates
open PrimitiveLineDualMeasure

section Product

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Canonical continuous product-dual coordinates, with quotient factor first. -/
def dualProductCoordinates :
    (StrongDual ℝ F × StrongDual ℝ E) ≃L[ℝ] StrongDual ℝ (E × F) :=
  (ContinuousLinearEquiv.prodComm ℝ (StrongDual ℝ F) (StrongDual ℝ E)).trans
    (ContinuousLinearMap.coprodEquivL ℝ)

@[simp]
theorem dualProductCoordinates_apply (g : StrongDual ℝ F × StrongDual ℝ E) (x : E × F) :
    dualProductCoordinates g x = g.2 x.1 + g.1 x.2 := rfl

/-- The actual integral dual of an actual product lattice has the literal product pullback. -/
theorem comap_integralDual_dualProductCoordinates (A : Submodule ℤ E) (B : Submodule ℤ F) :
    ZLattice.comap ℝ (integralDual (A.prod B)) dualProductCoordinates.toLinearMap =
      (integralDual B).prod (integralDual A) := by
  ext g
  change (∀ x ∈ A.prod B, dualProductCoordinates g x ∈
    LinearMap.range (Algebra.linearMap ℤ ℝ)) ↔
      (g.1 ∈ integralDual B ∧ g.2 ∈ integralDual A)
  constructor
  · intro hg
    constructor
    · intro b hb
      simpa only [dualProductCoordinates_apply, map_zero, zero_add] using
        hg (0, b) ⟨A.zero_mem, hb⟩
    · intro a ha
      simpa only [dualProductCoordinates_apply, map_zero, add_zero] using
        hg (a, 0) ⟨ha, B.zero_mem⟩
  · rintro ⟨hgB, hgA⟩ x hx
    exact (LinearMap.range (Algebra.linearMap ℤ ℝ)).add_mem
      (hgA x.1 hx.1) (hgB x.2 hx.2)

end Product

attribute [local instance] Submodule.closed_of_finiteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (U : Submodule ℝ E)
  (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U)

/-- Actual adapted continuous-dual coordinates, with the quotient dual first. -/
def dualAdaptedCoordinates :
    (StrongDual ℝ (E ⧸ U) × StrongDual ℝ U) ≃L[ℝ] StrongDual ℝ E :=
  dualProductCoordinates.trans
    ((adaptedCoordinates L U hU).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))

@[simp]
theorem dualAdaptedCoordinates_apply
    (g : StrongDual ℝ (E ⧸ U) × StrongDual ℝ U) (x : E) :
    dualAdaptedCoordinates L U hU g x =
      g.2 ((adaptedCoordinates L U hU).symm x).1 +
        g.1 ((adaptedCoordinates L U hU).symm x).2 := rfl

/-- The first dual coordinate is actual quotient pullback. -/
theorem dualAdaptedCoordinates_inl (g : StrongDual ℝ (E ⧸ U)) :
    dualAdaptedCoordinates L U hU (g, 0) = quotientPullback U g := by
  ext x
  have h := quotient_adaptedCoordinates L U hU ((adaptedCoordinates L U hU).symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  simp only [dualAdaptedCoordinates_apply, zero_apply, zero_add,
    quotientPullback_apply, h]

/-- Restriction of the actual adapted dual coordinate is its second component. -/
theorem dualRestriction_dualAdaptedCoordinates
    (g : StrongDual ℝ (E ⧸ U) × StrongDual ℝ U) :
    dualRestriction U (dualAdaptedCoordinates L U hU g) = g.2 := by
  ext u
  have h : (adaptedCoordinates L U hU).symm (u : E) = (u, 0) := by
    apply (adaptedCoordinates L U hU).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply, adaptedCoordinates_inl]
  simp only [dualRestriction_apply, dualAdaptedCoordinates_apply, h, map_zero, add_zero]

/-- The second inverse coordinate is the actual restriction, on all functionals. -/
theorem dualAdaptedCoordinates_symm_snd (f : StrongDual ℝ E) :
    ((dualAdaptedCoordinates L U hU).symm f).2 = dualRestriction U f := by
  have h := dualRestriction_dualAdaptedCoordinates L U hU
    ((dualAdaptedCoordinates L U hU).symm f)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The dual central section is the intrinsic polar of the actual quotient image. -/
theorem central_section_eq_quotient_polar (C : Set E) :
    ConvexCentralSection.sectionAt ((dualAdaptedCoordinates L U hU).symm ''
      StrongDual.polar ℝ C) 0 = StrongDual.polar ℝ (U.mkQ '' C) := by
  rw [ContinuousLinearEquiv.image_symm_eq_preimage]
  ext g
  change dualAdaptedCoordinates L U hU (g, 0) ∈ StrongDual.polar ℝ C ↔
    g ∈ StrongDual.polar ℝ (U.mkQ '' C)
  rw [dualAdaptedCoordinates_inl]
  change (∀ x ∈ C, ‖g (U.mkQ x)‖ ≤ 1) ↔ ∀ y ∈ U.mkQ '' C, ‖g y‖ ≤ 1
  constructor
  · rintro hg _ ⟨x, hx, rfl⟩
    exact hg x hx
  · intro hg x hx
    exact hg (U.mkQ x) ⟨x, hx, rfl⟩

/-- The second actual dual projection is precisely the restriction image. -/
theorem projection_eq_restriction_image (C : Set E) :
    Prod.snd '' ((dualAdaptedCoordinates L U hU).symm '' StrongDual.polar ℝ C) =
      dualRestriction U '' StrongDual.polar ℝ C := by
  rw [Set.image_image]
  congr 1
  funext f
  exact dualAdaptedCoordinates_symm_snd L U hU f

/-- The constructed actual dual coordinate has the actual quotient/intersection product
lattice as pullback; this identity is derived, rather than assumed as transport data. -/
theorem dualAdaptedCoordinates_comap :
    ZLattice.comap ℝ (integralDual L) (dualAdaptedCoordinates L U hU).toLinearMap =
      (integralDual (quotientImage L U)).prod
        (integralDual (intersectionAsSubmodule L U)) := by
  ext g
  change dualProductCoordinates g ∈ ZLattice.comap ℝ (integralDual L)
      ((adaptedCoordinates L U hU).arrowCongr
        (ContinuousLinearEquiv.refl ℝ ℝ)).toLinearMap ↔ _
  rw [comap_integralDual_arrowCongr, adaptedCoordinates_comap L U hU]
  change g ∈ ZLattice.comap ℝ
      (integralDual ((intersectionAsSubmodule L U).prod (quotientImage L U)))
      dualProductCoordinates.toLinearMap ↔ _
  rw [comap_integralDual_dualProductCoordinates]

include hU in
/-- Actual polar restriction to the actual rational subspace is the intrinsic section polar. -/
theorem restriction_image_polar_eq_section_polar
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    dualRestriction U '' StrongDual.polar ℝ C =
      StrongDual.polar ℝ (U.subtype ⁻¹' C) := by
  let e := adaptedCoordinates L U hU
  let d := e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have hcompactB : IsCompact (e ⁻¹' C) := by
    rw [← ContinuousLinearEquiv.image_symm_eq_preimage]
    exact hcompact.image e.symm.continuous
  have hconvexB : Convex ℝ (e ⁻¹' C) := hconvex.linear_preimage e.toLinearMap
  have hsymmB : ∀ z ∈ e ⁻¹' C, -z ∈ e ⁻¹' C := by
    intro z hz
    simpa only [mem_preimage, map_neg] using hsymm (e z) hz
  have hzeroB : (0 : U × (E ⧸ U)) ∈ interior (e ⁻¹' C) := by
    change (0 : U × (E ⧸ U)) ∈ interior (e.toHomeomorph ⁻¹' C)
    rw [← e.toHomeomorph.preimage_interior]
    change e 0 ∈ interior C
    simpa only [map_zero] using hzero
  have hrestrict : (fun f : StrongDual ℝ E =>
      (d.symm f).comp (ContinuousLinearMap.inl ℝ U (E ⧸ U))) = dualRestriction U := by
    funext f
    ext u
    change f (e (u, 0)) = f (u : E)
    rw [adaptedCoordinates_inl]
  have hpolar : d.symm '' StrongDual.polar ℝ C = StrongDual.polar ℝ (e ⁻¹' C) := by
    rw [ContinuousLinearEquiv.image_symm_eq_preimage]
    exact preimage_polar_arrowCongr e C
  have hsection : (fun u : U => (u, (0 : E ⧸ U))) ⁻¹' (e ⁻¹' C) =
      U.subtype ⁻¹' C := by
    ext u
    change e (u, 0) ∈ C ↔ (u : E) ∈ C
    rw [adaptedCoordinates_inl]
  calc
    _ = (fun g : StrongDual ℝ (U × (E ⧸ U)) =>
        g.comp (ContinuousLinearMap.inl ℝ U (E ⧸ U))) ''
          (d.symm '' StrongDual.polar ℝ C) := by rw [Set.image_image, hrestrict]
    _ = StrongDual.polar ℝ (U.subtype ⁻¹' C) := by
      rw [hpolar, polar_section_restriction_inl hcompactB hconvexB hsymmB hzeroB, hsection]

/-- The projected actual dual polar is the intrinsic polar of the literal central section. -/
theorem projection_eq_section_polar
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    Prod.snd '' ((dualAdaptedCoordinates L U hU).symm '' StrongDual.polar ℝ C) =
      StrongDual.polar ℝ (U.subtype ⁻¹' C) := by
  rw [projection_eq_restriction_image,
    restriction_image_polar_eq_section_polar L U hU hcompact hconvex hsymm hzero]

section Measure

variable [MeasurableSpace (StrongDual ℝ E)] [BorelSpace (StrongDual ℝ E)]
  [MeasurableSpace (StrongDual ℝ U)] [BorelSpace (StrongDual ℝ U)]
  [MeasurableSpace (StrongDual ℝ (E ⧸ U))] [BorelSpace (StrongDual ℝ (E ⧸ U))]

/-- The actual dual coordinates preserve actual normalized lattice measures, with no supplied
measure transport premise. -/
theorem measurePreserving_dualAdaptedCoordinates_normalizedMeasure
    (μ : Measure (StrongDual ℝ E)) [μ.IsAddHaarMeasure]
    (ν : Measure (StrongDual ℝ (E ⧸ U))) [ν.IsAddHaarMeasure]
    (ξ : Measure (StrongDual ℝ U)) [ξ.IsAddHaarMeasure] :
    MeasurePreserving (dualAdaptedCoordinates L U hU)
      ((latticeNormalizedMeasure (integralDual (quotientImage L U)) ν).prod
        (latticeNormalizedMeasure (integralDual (intersectionAsSubmodule L U)) ξ))
      (latticeNormalizedMeasure (integralDual L) μ) := by
  let := integralDual_discrete L
  let := integralDual_isZLattice L
  let := intersectionAsSubmodule_discrete L U hU
  let := intersectionAsSubmodule_isZLattice L U hU
  let := quotientImage_discrete L U hU
  let := quotientImage_isZLattice L U hU
  let := integralDual_discrete (intersectionAsSubmodule L U)
  let := integralDual_isZLattice (intersectionAsSubmodule L U)
  let := integralDual_discrete (quotientImage L U)
  let := integralDual_isZLattice (quotientImage L U)
  have h := measurePreserving_latticeNormalizedMeasure_comap (integralDual L)
    (dualAdaptedCoordinates L U hU) μ (ν.prod ξ)
  rw [dualAdaptedCoordinates_comap, latticeNormalizedMeasure_prod] at h
  exact h

include hU in
/-- Actual normalized polar volume is bounded by the actual quotient polar volume times the
actual intersection-section polar volume. -/
theorem normalizedMeasure_polar_le_quotient_mul_intersection
    (μ : Measure (StrongDual ℝ E)) [μ.IsAddHaarMeasure]
    (ν : Measure (StrongDual ℝ (E ⧸ U))) [ν.IsAddHaarMeasure]
    (ξ : Measure (StrongDual ℝ U)) [ξ.IsAddHaarMeasure]
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    latticeNormalizedMeasure (integralDual L) μ (StrongDual.polar ℝ C) ≤
      latticeNormalizedMeasure (integralDual (quotientImage L U)) ν
          (StrongDual.polar ℝ (U.mkQ '' C)) *
        latticeNormalizedMeasure (integralDual (intersectionAsSubmodule L U)) ξ
          (StrongDual.polar ℝ (U.subtype ⁻¹' C)) := by
  let := intersectionAsSubmodule_discrete L U hU
  let := intersectionAsSubmodule_isZLattice L U hU
  let := quotientImage_discrete L U hU
  let := quotientImage_isZLattice L U hU
  let := integralDual_discrete (intersectionAsSubmodule L U)
  let := integralDual_isZLattice (intersectionAsSubmodule L U)
  let := integralDual_discrete (quotientImage L U)
  let := integralDual_isZLattice (quotientImage L U)
  let := latticeNormalizedMeasure_isAddHaar (integralDual (intersectionAsSubmodule L U)) ξ
  let := latticeNormalizedMeasure_isAddHaar (integralDual (quotientImage L U)) ν
  have hMP := MeasurePreserving.symm
    (dualAdaptedCoordinates L U hU).toHomeomorph.toMeasurableEquiv
    (measurePreserving_dualAdaptedCoordinates_normalizedMeasure L U hU μ ν ξ)
  obtain ⟨hCp, hcCp, hsCp, _⟩ := polar_body_properties hcompact hconvex hsymm hzero
  have h := ConvexCentralSection.measure_le_central_mul_projection_of_measurePreserving
    (dualAdaptedCoordinates L U hU).symm (latticeNormalizedMeasure (integralDual L) μ)
    (latticeNormalizedMeasure (integralDual (quotientImage L U)) ν)
    (latticeNormalizedMeasure (integralDual (intersectionAsSubmodule L U)) ξ)
    hMP hCp hcCp hsCp
  simpa only [central_section_eq_quotient_polar L U hU,
    projection_eq_section_polar L U hU hcompact hconvex hsymm hzero] using h

end Measure

end ArakelovGeometry.GeometryOfNumbers.LatticeDualCentralSection

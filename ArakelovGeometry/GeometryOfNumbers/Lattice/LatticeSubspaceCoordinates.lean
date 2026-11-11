/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.Lattice.LatticeSubspaceQuotient
public import ArakelovGeometry.GeometryOfNumbers.Measure.LatticeNormalizedMeasure
import ArakelovGeometry.GeometryOfNumbers.Measure.LatticeNormalizedMeasureEquiv
import ArakelovGeometry.GeometryOfNumbers.Measure.LatticeNormalizedProductMeasure

/-! # Actual adapted subspace and quotient coordinates for a rational lattice subspace -/

@[expose] public section

noncomputable section
open Module MeasureTheory

namespace ArakelovGeometry.GeometryOfNumbers.LatticeSubspaceCoordinates

open LatticeSubspaceBasis LatticeSubspaceQuotient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (U : Submodule ℝ E)

attribute [local instance] Submodule.closed_of_finiteDimensional

/-- The actual intersection lattice, inside the actual real subspace. -/
def intersectionAsSubmodule : Submodule ℤ U :=
  L.comap (U.subtype.restrictScalars ℤ)

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] in
@[simp]
theorem mem_intersectionAsSubmodule (u : U) :
    u ∈ intersectionAsSubmodule L U ↔ (u : E) ∈ L := Iff.rfl

/-- The integer span of the actual intersection basis is the actual intersection lattice. -/
theorem intersectionAsSubmodule_eq_span
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    intersectionAsSubmodule L U =
      Submodule.span ℤ (Set.range (intersectionRealBasis L U hU)) := by
  apply Submodule.map_injective_of_injective
    (f := U.subtype.restrictScalars ℤ) Subtype.val_injective
  rw [Submodule.map_span, ← Set.range_comp]
  have hf : (U.subtype.restrictScalars ℤ) ∘ intersectionRealBasis L U hU =
      fun i => ((intersectionBasis L U i : L) : E) := by
    funext i
    exact intersectionRealBasis_apply L U hU i
  rw [hf, intersectionBasis_integerSpan]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hu, u.property⟩
  · rintro ⟨hxL, hxU⟩
    exact ⟨⟨x, hxU⟩, hxL, rfl⟩

/-- Actual adapted coordinates, constructed by matching the actual product and ambient bases. -/
def adaptedCoordinates
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    (U × (E ⧸ U)) ≃L[ℝ] E :=
  (((intersectionRealBasis L U hU).prod (quotientRealBasis L U hU)).equiv
    (realAdaptedBasis L U) (Equiv.refl _)).toContinuousLinearEquiv

theorem adaptedCoordinates_basis
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U)
    (i : Fin (Module.finrank ℤ (intersection L U)) ⊕
      Fin (Module.finrank ℤ (L ⧸ intersection L U))) :
    adaptedCoordinates L U hU
      (((intersectionRealBasis L U hU).prod (quotientRealBasis L U hU)) i) =
      realAdaptedBasis L U i :=
  Basis.equiv_apply _ i _ (Equiv.refl _)

@[simp]
theorem adaptedCoordinates_inl_basis
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U)
    (i : Fin (Module.finrank ℤ (intersection L U))) :
    adaptedCoordinates L U hU (intersectionRealBasis L U hU i, 0) =
      (intersectionRealBasis L U hU i : E) := by
  simpa [Basis.prod_apply] using adaptedCoordinates_basis L U hU (Sum.inl i)

@[simp]
theorem adaptedCoordinates_inr_basis
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U)
    (j : Fin (Module.finrank ℤ (L ⧸ intersection L U))) :
    adaptedCoordinates L U hU (0, quotientRealBasis L U hU j) =
      realAdaptedBasis L U (Sum.inr j) := by
  simpa [Basis.prod_apply] using adaptedCoordinates_basis L U hU (Sum.inr j)

@[simp]
theorem adaptedCoordinates_inl
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) (u : U) :
    adaptedCoordinates L U hU (u, 0) = (u : E) := by
  have h : (adaptedCoordinates L U hU).toLinearMap.comp
      (LinearMap.inl ℝ U (E ⧸ U)) = U.subtype := by
    apply (intersectionRealBasis L U hU).ext
    intro i
    exact adaptedCoordinates_inl_basis L U hU i
  exact LinearMap.congr_fun h u

@[simp]
theorem quotient_adaptedCoordinates
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U)
    (x : U × (E ⧸ U)) :
    U.mkQ (adaptedCoordinates L U hU x) = x.2 := by
  have h : U.mkQ.comp (adaptedCoordinates L U hU).toLinearMap =
      LinearMap.snd ℝ U (E ⧸ U) := by
    apply ((intersectionRealBasis L U hU).prod (quotientRealBasis L U hU)).ext
    intro i
    change U.mkQ (adaptedCoordinates L U hU
      (((intersectionRealBasis L U hU).prod (quotientRealBasis L U hU)) i)) = _
    rw [adaptedCoordinates_basis]
    rcases i with i | j
    · simp only [realAdaptedBasis_inl, Submodule.mkQ_apply, Basis.prod_apply,
        LinearMap.coe_inl, LinearMap.coe_inr, Sum.elim_inl, Function.comp_apply,
        LinearMap.snd_apply, Submodule.Quotient.mk_eq_zero]
      exact (intersectionBasis L U i).property
    · simp [Basis.prod_apply, quotientRealBasis_apply]
  exact LinearMap.congr_fun h x

/-- Discreteness of the actual intersection lattice is derived from its proved basis span. -/
theorem intersectionAsSubmodule_discrete
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    DiscreteTopology (intersectionAsSubmodule L U) := by
  rw [intersectionAsSubmodule_eq_span L U hU]
  infer_instance

/-- Fullness of the actual intersection lattice follows from its actual real basis. -/
theorem intersectionAsSubmodule_isZLattice
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    letI := intersectionAsSubmodule_discrete L U hU
    IsZLattice ℝ (intersectionAsSubmodule L U) := by
  let := intersectionAsSubmodule_discrete L U hU
  constructor
  rw [intersectionAsSubmodule_eq_span L U hU]
  exact ZSpan.span_top (intersectionRealBasis L U hU)

/-- The canonical pullback of the original lattice is the literal product of its intersection
and actual quotient-image lattices. No splitting or product equality is assumed. -/
theorem adaptedCoordinates_comap
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    ZLattice.comap ℝ L (adaptedCoordinates L U hU).toLinearMap =
      (intersectionAsSubmodule L U).prod (quotientImage L U) := by
  let e := adaptedCoordinates L U hU
  let f := e.toLinearMap.restrictScalars ℤ
  apply Submodule.map_injective_of_injective (f := f) e.injective
  change (L.comap f).map f = _
  rw [Submodule.map_comap_eq_self (by
    intro x _
    exact ⟨e.symm x, e.apply_symm_apply x⟩)]
  rw [intersectionAsSubmodule_eq_span L U hU, quotientImage_eq_span L U hU,
    ← integerSpan_prod_basis, Submodule.map_span, ← Set.range_comp]
  have hf : f ∘ ((intersectionRealBasis L U hU).prod (quotientRealBasis L U hU)) =
      realAdaptedBasis L U := by
    funext i
    exact adaptedCoordinates_basis L U hU i
  rw [hf]
  exact ((adaptedBasis L U).ofZLatticeBasis_span ℝ).symm

section Measure

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace (E ⧸ U)] [BorelSpace (E ⧸ U)]
  (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U)
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  (ν : Measure U) [Measure.IsAddHaarMeasure ν]
  (ξ : Measure (E ⧸ U)) [Measure.IsAddHaarMeasure ξ]

/-- Actual adapted coordinates carry the product of the two actual normalized measures to
the actual normalized measure of the original lattice, including rank zero. -/
theorem map_adaptedCoordinates_normalizedMeasure :
    Measure.map (adaptedCoordinates L U hU)
      ((latticeNormalizedMeasure (intersectionAsSubmodule L U) ν).prod
        (latticeNormalizedMeasure (quotientImage L U) ξ)) =
      latticeNormalizedMeasure L μ := by
  let := intersectionAsSubmodule_discrete L U hU
  let := intersectionAsSubmodule_isZLattice L U hU
  let := quotientImage_discrete L U hU
  let := quotientImage_isZLattice L U hU
  rw [← latticeNormalizedMeasure_prod, ← adaptedCoordinates_comap L U hU]
  exact map_latticeNormalizedMeasure_comap L (adaptedCoordinates L U hU) μ (ν.prod ξ)

/-- The constructed actual adapted coordinates are measure preserving for normalized measures. -/
theorem measurePreserving_adaptedCoordinates_normalizedMeasure :
    MeasurePreserving (adaptedCoordinates L U hU)
      ((latticeNormalizedMeasure (intersectionAsSubmodule L U) ν).prod
        (latticeNormalizedMeasure (quotientImage L U) ξ))
      (latticeNormalizedMeasure L μ) :=
  ⟨(adaptedCoordinates L U hU).continuous.measurable,
    map_adaptedCoordinates_normalizedMeasure L U hU μ ν ξ⟩

/-- A measurable set has its actual product-coordinate normalized measure. -/
theorem adaptedCoordinates_normalizedMeasure_preimage {A : Set E} (hA : MeasurableSet A) :
    ((latticeNormalizedMeasure (intersectionAsSubmodule L U) ν).prod
      (latticeNormalizedMeasure (quotientImage L U) ξ))
        (adaptedCoordinates L U hU ⁻¹' A) = latticeNormalizedMeasure L μ A := by
  have h := congrArg (fun τ : Measure E => τ A)
    (map_adaptedCoordinates_normalizedMeasure L U hU μ ν ξ)
  rw [Measure.map_apply (adaptedCoordinates L U hU).continuous.measurable hA] at h
  exact h

end Measure

end ArakelovGeometry.GeometryOfNumbers.LatticeSubspaceCoordinates

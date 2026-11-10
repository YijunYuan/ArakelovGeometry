/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.IntegralDualCovolume
public import ArakelovGeometry.GeometryOfNumbers.LatticeSubspaceCoordinates
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! # Actual integral subspace projections and integral dual coordinates -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.LatticeIntegralDualCoordinates

open LatticeSubspaceBasis LatticeSubspaceCoordinates

section DualMaps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Submodule ℝ E)

/-- Pullback on the actual continuous dual along the actual quotient map. -/
def quotientPullback : StrongDual ℝ (E ⧸ U) →L[ℝ] StrongDual ℝ E :=
  (ContinuousLinearMap.compL ℝ E (E ⧸ U) ℝ).flip U.mkQL

@[simp]
theorem quotientPullback_apply (g : StrongDual ℝ (E ⧸ U)) (x : E) :
    quotientPullback U g x = g (U.mkQ x) := rfl

/-- Restriction on the actual continuous dual along the actual subspace inclusion. -/
def dualRestriction : StrongDual ℝ E →L[ℝ] StrongDual ℝ U :=
  (ContinuousLinearMap.compL ℝ U E ℝ).flip U.subtypeL

@[simp]
theorem dualRestriction_apply (f : StrongDual ℝ E) (u : U) :
    dualRestriction U f u = f (u : E) := rfl

/-- Pullback is injective because the actual quotient map is surjective. -/
theorem quotientPullback_injective : Function.Injective (quotientPullback U) := by
  intro f g h
  ext q
  obtain ⟨x, rfl⟩ := U.mkQ_surjective q
  exact congrArg (fun k : StrongDual ℝ E => k x) h

/-- The actual continuous quotient dual is precisely the kernel of restriction. -/
theorem quotientPullback_range :
    LinearMap.range (quotientPullback U).toLinearMap =
      LinearMap.ker (dualRestriction U).toLinearMap := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change dualRestriction U (quotientPullback U g) = 0
    ext u
    change g (U.mkQ (u : E)) = 0
    rw [show U.mkQ (u : E) = 0 from (Submodule.Quotient.mk_eq_zero U).mpr u.property,
      map_zero]
  · intro hf
    change dualRestriction U f = 0 at hf
    have hU : U ≤ f.ker := by
      intro x hx
      exact congrArg (fun g : StrongDual ℝ U => g ⟨x, hx⟩) hf
    refine ⟨U.liftQL f hU, ?_⟩
    ext x
    rfl

end DualMaps

section IntegralDual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : Submodule ℤ E) (U : Submodule ℝ E)

/-- Restriction is integer valued on the actual intersection whenever the original
functional is integer valued on the original lattice. -/
theorem dualRestriction_mem_integralDual {f : StrongDual ℝ E} (hf : f ∈ integralDual L) :
    dualRestriction U f ∈ integralDual (intersectionAsSubmodule L U) := by
  intro u hu
  exact hf (u : E) hu

variable [FiniteDimensional ℝ E]

attribute [local instance] Submodule.closed_of_finiteDimensional

/-- Integrality on the literal quotient image is exactly integrality of the pullback. -/
theorem mem_integralDual_quotient (g : StrongDual ℝ (E ⧸ U)) :
    g ∈ integralDual (quotientImage L U) ↔ quotientPullback U g ∈ integralDual L := by
  constructor
  · intro hg x hx
    exact hg (U.mkQ x) ⟨x, hx, rfl⟩
  · intro hg q hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact hg x hx

/-- The actual quotient-image integral dual pulls back onto the integral annihilator
inside the original continuous dual. No lattice or rationality assumptions are needed. -/
theorem integralDual_quotient_image :
    (integralDual (quotientImage L U)).map
        ((quotientPullback U).toLinearMap.restrictScalars ℤ) =
      integralDual L ⊓ LinearMap.ker ((dualRestriction U).toLinearMap.restrictScalars ℤ) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(mem_integralDual_quotient L U g).mp hg, ?_⟩
    have hk : quotientPullback U g ∈ LinearMap.range (quotientPullback U).toLinearMap :=
      ⟨g, rfl⟩
    rw [quotientPullback_range U] at hk
    exact hk
  · rintro ⟨hf, hk⟩
    change f ∈ LinearMap.ker (dualRestriction U).toLinearMap at hk
    rw [← quotientPullback_range U] at hk
    obtain ⟨g, hg⟩ := hk
    refine ⟨g, (mem_integralDual_quotient L U g).mpr ?_, hg⟩
    change quotientPullback U g = f at hg
    rw [hg]
    exact hf

end IntegralDual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (U : Submodule ℝ E)

attribute [local instance] Submodule.closed_of_finiteDimensional

/-- The actual subspace projection constructed from the adapted coordinates of the original
lattice, with its original subspace norm. -/
def integralProjection
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) : E →L[ℝ] U :=
  (ContinuousLinearMap.fst ℝ U (E ⧸ U)).comp
    (adaptedCoordinates L U hU).symm.toContinuousLinearMap

@[simp]
theorem integralProjection_coe
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) (u : U) :
    integralProjection L U hU (u : E) = u := by
  change ((adaptedCoordinates L U hU).symm (u : E)).1 = u
  rw [← adaptedCoordinates_inl L U hU u, ContinuousLinearEquiv.symm_apply_apply]

/-- This actual projection takes original lattice points into the actual intersection lattice. -/
theorem integralProjection_mem_intersection
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U)
    {x : E} (hx : x ∈ L) :
    integralProjection L U hU x ∈ intersectionAsSubmodule L U := by
  have h : (adaptedCoordinates L U hU).symm x ∈
      (intersectionAsSubmodule L U).prod (quotientImage L U) := by
    rw [← adaptedCoordinates_comap L U hU]
    change adaptedCoordinates L U hU ((adaptedCoordinates L U hU).symm x) ∈ L
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx
  exact h.1

/-- The actual restriction image equals the actual intersection integral dual.
An extension is constructed by the integral projection, with the original norms. -/
theorem integralDual_restriction_image
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    (integralDual L).map ((dualRestriction U).toLinearMap.restrictScalars ℤ) =
      integralDual (intersectionAsSubmodule L U) := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact dualRestriction_mem_integralDual L U hf
  · intro hg
    let f : StrongDual ℝ E := g.comp (integralProjection L U hU)
    have hf : f ∈ integralDual L := by
      intro x hx
      exact hg _ (integralProjection_mem_intersection L U hU hx)
    refine ⟨f, hf, ?_⟩
    ext u
    change g (integralProjection L U hU (u : E)) = g u
    rw [integralProjection_coe]

end ArakelovGeometry.GeometryOfNumbers.LatticeIntegralDualCoordinates

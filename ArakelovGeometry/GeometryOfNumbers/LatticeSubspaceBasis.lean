/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Integral bases adapted to an actual lattice intersection -/

noncomputable section
open Module

namespace ArakelovGeometry.GeometryOfNumbers.LatticeSubspaceBasis

section Algebraic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  (L : Submodule ℤ E) (U : Submodule ℝ E)

/-- The literal intersection, regarded as an integer submodule of L. -/
def intersection : Submodule ℤ L :=
  (U.restrictScalars ℤ).comap L.subtype

@[simp]
theorem mem_intersection (x : L) :
    x ∈ intersection L U ↔ (x : E) ∈ U := Iff.rfl

/-- The canonical map of the actual integer quotient into the real quotient. -/
def quotientInclusion : (L ⧸ intersection L U) →ₗ[ℤ] (E ⧸ U) :=
  (intersection L U).liftQ
    ((U.mkQ.restrictScalars ℤ).comp L.subtype) (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero U).2 hx)

@[simp]
theorem quotientInclusion_mk (x : L) :
    quotientInclusion L U ((intersection L U).mkQ x) = U.mkQ (x : E) := rfl

theorem quotientInclusion_injective :
    Function.Injective (quotientInclusion L U) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  intro x hx
  exact (Submodule.Quotient.mk_eq_zero U).1 hx

/-- Torsion-freeness is derived from the canonical injection into the real quotient. -/
theorem quotient_isTorsionFree : Module.IsTorsionFree ℤ (L ⧸ intersection L U) := by
  let : Module.IsTorsionFree ℤ (E ⧸ U) := Module.IsTorsionFree.trans ℝ
  exact (quotientInclusion_injective L U).moduleIsTorsionFree
    (quotientInclusion L U) (fun n x => (quotientInclusion L U).map_smul n x)

theorem intersection_saturated (n : ℤ) (hn : n ≠ 0) (x : L)
    (hx : n • x ∈ intersection L U) : x ∈ intersection L U := by
  let := quotient_isTorsionFree L U
  apply (Submodule.Quotient.mk_eq_zero (intersection L U)).1
  apply (smul_eq_zero_iff_right hn).1
  exact ((intersection L U).mkQ.map_smul n x).symm.trans
    ((Submodule.Quotient.mk_eq_zero (intersection L U)).2 hx)

/-- The literal image of the original lattice in the actual real quotient. -/
def quotientImage : Submodule ℤ (E ⧸ U) :=
  L.map (U.mkQ.restrictScalars ℤ)

theorem quotientInclusion_range :
    (quotientInclusion L U).range = quotientImage L U := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := (intersection L U).mkQ_surjective q
    exact ⟨(x : E), x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(intersection L U).mkQ ⟨x, hx⟩, rfl⟩

/-- The actual quotient and actual quotient-image lattice are canonically isomorphic. -/
def quotientEquivImage : (L ⧸ intersection L U) ≃ₗ[ℤ] quotientImage L U :=
  (LinearEquiv.ofInjective (quotientInclusion L U) (quotientInclusion_injective L U)).trans
    (LinearEquiv.ofEq _ _ (quotientInclusion_range L U))

@[simp]
theorem quotientEquivImage_coe (x : L ⧸ intersection L U) :
    (quotientEquivImage L U x : E ⧸ U) = quotientInclusion L U x := rfl

theorem quotientImage_span_top (hL : Submodule.span ℝ (L : Set E) = ⊤) :
    Submodule.span ℝ (quotientImage L U : Set (E ⧸ U)) = ⊤ := by
  rw [quotientImage, Submodule.map_coe]
  change Submodule.span ℝ (U.mkQ '' (L : Set E)) = ⊤
  rw [← Submodule.map_span, hL, Submodule.map_top, Submodule.range_mkQ]

section Finite

variable [Module.Finite ℤ L]

/-- An actual finite integer basis of the literal intersection. -/
def intersectionBasis :
    Basis (Fin (Module.finrank ℤ (intersection L U))) ℤ (intersection L U) := by
  letI : Module.IsTorsionFree ℤ E := Module.IsTorsionFree.trans ℝ
  exact Module.finBasis ℤ (intersection L U)

/-- An actual finite integer basis of the quotient, after deriving torsion-freeness. -/
def quotientBasis :
    Basis (Fin (Module.finrank ℤ (L ⧸ intersection L U))) ℤ (L ⧸ intersection L U) := by
  letI := quotient_isTorsionFree L U
  exact Module.finBasis ℤ (L ⧸ intersection L U)

/-- The constructed adapted basis of the original lattice. -/
def adaptedBasis :
    Basis (Fin (Module.finrank ℤ (intersection L U)) ⊕
      Fin (Module.finrank ℤ (L ⧸ intersection L U))) ℤ L :=
  (intersectionBasis L U).sumQuot (quotientBasis L U)

@[simp]
theorem adaptedBasis_inl (i : Fin (Module.finrank ℤ (intersection L U))) :
    adaptedBasis L U (Sum.inl i) = (intersectionBasis L U i : L) := by
  exact Basis.sumQuot_inl _ _ i

@[simp]
theorem adaptedBasis_quotient_inr
    (j : Fin (Module.finrank ℤ (L ⧸ intersection L U))) :
    (intersection L U).mkQ (adaptedBasis L U (Sum.inr j)) = quotientBasis L U j := by
  exact Basis.sumQuot_inr _ _ j

theorem adaptedBasis_repr_inr (x : L)
    (j : Fin (Module.finrank ℤ (L ⧸ intersection L U))) :
    (adaptedBasis L U).repr x (Sum.inr j) =
      (quotientBasis L U).repr ((intersection L U).mkQ x) j :=
  Basis.sumQuot_repr_inr _ _ x j

theorem mem_intersection_iff_repr_inr_eq_zero (x : L) :
    x ∈ intersection L U ↔
      ∀ j, (adaptedBasis L U).repr x (Sum.inr j) = 0 := by
  simp only [adaptedBasis_repr_inr]
  rw [← (Submodule.Quotient.mk_eq_zero (intersection L U))]
  constructor
  · intro hx j
    simp [hx]
  · intro hx
    apply (quotientBasis L U).repr.injective
    ext j
    simpa using hx j

/-- Finite generation of the actual image follows from that of the original lattice. -/
theorem quotientImage_finite : Module.Finite ℤ (quotientImage L U) := by
  change Module.Finite ℤ (L.map (U.mkQ.restrictScalars ℤ))
  infer_instance

/-- An actual integer basis of the original lattice image in the real quotient. -/
def quotientImageBasis :
    Basis (Fin (Module.finrank ℤ (L ⧸ intersection L U))) ℤ (quotientImage L U) :=
  (quotientBasis L U).map (quotientEquivImage L U)

theorem quotientImageBasis_apply
    (j : Fin (Module.finrank ℤ (L ⧸ intersection L U))) :
    (quotientImageBasis L U j : E ⧸ U) =
      U.mkQ (adaptedBasis L U (Sum.inr j) : E) := by
  rw [← quotientInclusion_mk, adaptedBasis_quotient_inr]
  rfl


theorem intersectionBasis_integerSpan :
    Submodule.span ℤ (Set.range fun i => ((intersectionBasis L U i : L) : E)) =
      L ⊓ U.restrictScalars ℤ := by
  let f : intersection L U →ₗ[ℤ] E :=
    L.subtype.comp (intersection L U).subtype
  calc
    _ = (Submodule.span ℤ (Set.range (intersectionBasis L U))).map f := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = f.range := by rw [(intersectionBasis L U).span_eq, Submodule.map_top]
    _ = L ⊓ U.restrictScalars ℤ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y.val.property, y.property⟩
      · rintro ⟨hxL, hxU⟩
        exact ⟨⟨⟨x, hxL⟩, hxU⟩, rfl⟩

theorem intersectionBasis_realSpan
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    Submodule.span ℝ (Set.range fun i => ((intersectionBasis L U i : L) : E)) = U := by
  rw [← Submodule.span_span_of_tower (R := ℤ), intersectionBasis_integerSpan]
  exact hU

end Finite

end Algebraic


section RealCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (U : Submodule ℝ E)

/-- The actual constructed integral basis is also a real basis of the original ambient space. -/
def realAdaptedBasis :
    Basis (Fin (Module.finrank ℤ (intersection L U)) ⊕
      Fin (Module.finrank ℤ (L ⧸ intersection L U))) ℝ E :=
  (adaptedBasis L U).ofZLatticeBasis ℝ L

@[simp]
theorem realAdaptedBasis_inl (i : Fin (Module.finrank ℤ (intersection L U))) :
    realAdaptedBasis L U (Sum.inl i) = ((intersectionBasis L U i : L) : E) := by
  simp [realAdaptedBasis]

theorem realAdaptedBasis_left_span
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    Submodule.span ℝ (Set.range fun i => realAdaptedBasis L U (Sum.inl i)) = U := by
  simpa only [realAdaptedBasis_inl] using intersectionBasis_realSpan L U hU

/-- The left block is an actual real basis of U under precisely the source span premise. -/
def intersectionRealBasis
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    Basis (Fin (Module.finrank ℤ (intersection L U))) ℝ U :=
  (Basis.span ((realAdaptedBasis L U).linearIndependent.comp Sum.inl Sum.inl_injective)).map
    (LinearEquiv.ofEq _ _ (realAdaptedBasis_left_span L U hU))

@[simp]
theorem intersectionRealBasis_apply
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U)
    (i : Fin (Module.finrank ℤ (intersection L U))) :
    (intersectionRealBasis L U hU i : E) = ((intersectionBasis L U i : L) : E) := by
  simp [intersectionRealBasis, Basis.span_apply]

end RealCoordinates

end ArakelovGeometry.GeometryOfNumbers.LatticeSubspaceBasis

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.GeometryOfNumbers.LatticeSubspaceBasis
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Projection

/-! # The actual projected lattice in a rational real quotient -/

noncomputable section
open Module

namespace ArakelovGeometry.GeometryOfNumbers.LatticeSubspaceQuotient

open LatticeSubspaceBasis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (U : Submodule ℝ E)

attribute [local instance] Submodule.closed_of_finiteDimensional

/-- The right-block span of the already constructed basis of the actual original lattice. -/
def complementarySubspace : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun j => realAdaptedBasis L U (Sum.inr j))

/-- The complement is proved from the original source span premise, never supplied. -/
theorem intersection_isCompl_complement
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    IsCompl U (complementarySubspace L U) := by
  have h := (realAdaptedBasis L U).linearIndependent.isCompl_span_image
    (realAdaptedBasis L U).span_eq Set.isCompl_range_inl_range_inr
  simp only [← Set.range_comp, Function.comp_def] at h
  rw [realAdaptedBasis_left_span L U hU] at h
  exact h

/-- The actual right-block real basis of the constructed complementary subspace. -/
def complementaryBasis :
    Basis (Fin (Module.finrank ℤ (L ⧸ intersection L U))) ℝ (complementarySubspace L U) :=
  Basis.span ((realAdaptedBasis L U).linearIndependent.comp Sum.inr Sum.inr_injective)

@[simp]
theorem complementaryBasis_apply
    (j : Fin (Module.finrank ℤ (L ⧸ intersection L U))) :
    (complementaryBasis L U j : E) = realAdaptedBasis L U (Sum.inr j) := by
  exact congrArg Subtype.val (Basis.span_apply
    ((realAdaptedBasis L U).linearIndependent.comp Sum.inr Sum.inr_injective) j)

/-- A real basis of the literal quotient E/U, constructed from the actual adapted basis. -/
def quotientRealBasis
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    Basis (Fin (Module.finrank ℤ (L ⧸ intersection L U))) ℝ (E ⧸ U) :=
  (complementaryBasis L U).map
    (U.quotientEquivOfIsCompl (complementarySubspace L U)
      (intersection_isCompl_complement L U hU)).symm

@[simp]
theorem quotientRealBasis_apply
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U)
    (j : Fin (Module.finrank ℤ (L ⧸ intersection L U))) :
    quotientRealBasis L U hU j = U.mkQ (realAdaptedBasis L U (Sum.inr j)) := by
  change U.mkQ (complementaryBasis L U j : E) = _
  rw [complementaryBasis_apply]

/-- The actual original quotient-image lattice is the integer span of the constructed
real quotient basis, inside the actual quotient vector space. -/
theorem quotientImage_eq_span
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    quotientImage L U = Submodule.span ℤ (Set.range (quotientRealBasis L U hU)) := by
  have hf : (fun j => (quotientImageBasis L U j : E ⧸ U)) = quotientRealBasis L U hU := by
    funext j
    rw [quotientImageBasis_apply, quotientRealBasis_apply]
    simp [realAdaptedBasis]
  calc
    quotientImage L U =
        (Submodule.span ℤ (Set.range (quotientImageBasis L U))).map
          (quotientImage L U).subtype := by
      rw [(quotientImageBasis L U).span_eq, Submodule.map_subtype_top]
    _ = Submodule.span ℤ (Set.range fun j => (quotientImageBasis L U j : E ⧸ U)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = _ := by rw [hf]

/-- Discreteness is derived in the canonical quotient topology from the proved basis span. -/
theorem quotientImage_discrete
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    DiscreteTopology (quotientImage L U) := by
  rw [quotientImage_eq_span L U hU]
  infer_instance

/-- The actual projected lattice is full after its discreteness has been proved. -/
theorem quotientImage_isZLattice
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    letI := quotientImage_discrete L U hU
    IsZLattice ℝ (quotientImage L U) := by
  let := quotientImage_discrete L U hU
  exact ⟨quotientImage_span_top L U (inferInstance : IsZLattice ℝ L).span_top⟩

theorem quotientRealBasis_finrank
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    Module.finrank ℝ (E ⧸ U) = Module.finrank ℤ (L ⧸ intersection L U) := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (quotientRealBasis L U hU)

/-- A substantive lattice-rank consumer of the actual derived quotient-lattice structure. -/
theorem quotientImage_finrank
    (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U) :
    Module.finrank ℤ (quotientImage L U) = Module.finrank ℝ (E ⧸ U) := by
  let := quotientImage_discrete L U hU
  let := quotientImage_isZLattice L U hU
  exact ZLattice.rank ℝ (quotientImage L U)

end ArakelovGeometry.GeometryOfNumbers.LatticeSubspaceQuotient

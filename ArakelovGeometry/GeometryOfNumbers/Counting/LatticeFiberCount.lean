/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.Lattice.LatticeSubspaceCoordinates
import ArakelovGeometry.GeometryOfNumbers.Counting.LatticeCount

/-! # Counts of actual integer fibres in adapted lattice coordinates -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.LatticeFiberCount

open Set LatticeSubspaceBasis LatticeSubspaceQuotient LatticeSubspaceCoordinates

attribute [local instance] Submodule.closed_of_finiteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (U : Submodule ℝ E)
  (hU : Submodule.span ℝ ((L : Set E) ∩ (U : Set E)) = U)

/-- Literal lattice membership in the actual adapted coordinates. -/
theorem mem_adaptedCoordinates_iff (u : U) (q : E ⧸ U) :
    adaptedCoordinates L U hU (u, q) ∈ L ↔
      u ∈ intersectionAsSubmodule L U ∧ q ∈ quotientImage L U := by
  change (u, q) ∈ ZLattice.comap ℝ L (adaptedCoordinates L U hU).toLinearMap ↔ _
  rw [adaptedCoordinates_comap L U hU]
  rfl

/-- Actual quotient-lattice points in the literal quotient image of the body. -/
def quotientPoints (C : Set E) :=
  {q : quotientImage L U // (q : E ⧸ U) ∈ U.mkQ '' C}

/-- Actual intersection-lattice points in one actual adapted affine fibre. -/
def fiberPoints (C : Set E) (q : quotientPoints L U C) :=
  {u : intersectionAsSubmodule L U //
    adaptedCoordinates L U hU ((u : U), (q.val : E ⧸ U)) ∈ C}

/-- The original body points decompose into the actual integer fibres, including empty ones. -/
def bodyPointsEquivSigma (C : Set E) :
    {x : L // (x : E) ∈ C} ≃
      Σ q : quotientPoints L U C, fiberPoints L U hU C q where
  toFun x := by
    let e := adaptedCoordinates L U hU
    let p := e.symm (x.val : E)
    have hp := (mem_adaptedCoordinates_iff L U hU p.1 p.2).1
      (by simpa only [p, e, Prod.eta, ContinuousLinearEquiv.apply_symm_apply] using x.val.property)
    have hq : p.2 ∈ U.mkQ '' C := by
      refine ⟨(x.val : E), x.property, ?_⟩
      have h := quotient_adaptedCoordinates L U hU p
      simpa [p, e] using h
    exact ⟨⟨⟨p.2, hp.2⟩, hq⟩,
      ⟨⟨p.1, hp.1⟩, by simpa [p, e] using x.property⟩⟩
  invFun y :=
    ⟨⟨adaptedCoordinates L U hU ((y.2.val : U), (y.1.val : E ⧸ U)),
      (mem_adaptedCoordinates_iff L U hU _ _).2
        ⟨y.2.val.property, y.1.val.property⟩⟩, y.2.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (adaptedCoordinates L U hU).apply_symm_apply (x.val : E)
  right_inv y := by
    rcases y with ⟨⟨⟨q, hq⟩, hqC⟩, ⟨⟨u, hu⟩, huC⟩⟩
    dsimp
    apply Sigma.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg Prod.snd ((adaptedCoordinates L U hU).symm_apply_apply (u, q))
    · apply (Subtype.heq_iff_coe_eq (fun z => by
        change adaptedCoordinates L U hU
            ((z : U), ((adaptedCoordinates L U hU).symm
              (adaptedCoordinates L U hU (u, q))).2) ∈ C ↔
          adaptedCoordinates L U hU ((z : U), q) ∈ C
        rw [(adaptedCoordinates L U hU).symm_apply_apply])).mpr
      exact Subtype.ext
        (congrArg Prod.fst ((adaptedCoordinates L U hU).symm_apply_apply (u, q)))

omit [IsZLattice ℝ L] in
/-- Compactness gives finiteness of the actual original lattice-point type. -/
theorem finite_bodyPoints {C : Set E} (hC : IsCompact C) :
    Finite {x : L // (x : E) ∈ C} :=
  (LatticeCount.finite_subgroup_points_of_bounded L.toAddSubgroup hC.isBounded).to_subtype

include hU in
/-- Compactness and the derived quotient-lattice discreteness give actual quotient finiteness. -/
theorem finite_quotientPoints {C : Set E} (hC : IsCompact C) :
    Finite (quotientPoints L U C) := by
  let := quotientImage_discrete L U hU
  exact (LatticeCount.finite_subgroup_points_of_bounded (quotientImage L U).toAddSubgroup
    (hC.image U.continuous_mkQ).isBounded).to_subtype

/-- Each actual affine integer fibre injects into the original finite body-point set. -/
theorem finite_fiberPoints {C : Set E} (hC : IsCompact C) (q : quotientPoints L U C) :
    Finite (fiberPoints L U hU C q) := by
  let := finite_bodyPoints L hC
  apply Finite.of_injective (fun u : fiberPoints L U hU C q =>
    (bodyPointsEquivSigma L U hU C).symm ⟨q, u⟩)
  intro a b hab
  have h := congrArg (fun x : {x : L // (x : E) ∈ C} => (x.val : E)) hab
  have hp := (adaptedCoordinates L U hU).injective h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Prod.fst hp

include hU in
/-- The finite type is constructed from the actual compact quotient-point set. -/
@[instance_reducible]
def quotientPointsFintype {C : Set E} (hC : IsCompact C) :
    Fintype (quotientPoints L U C) := by
  let := finite_quotientPoints L U hU hC
  exact Fintype.ofFinite _

/-- The actual original count is the finite sum of its actual intersection-lattice fibres. -/
theorem card_body_eq_sum_fiber {C : Set E} (hC : IsCompact C) :
    letI := quotientPointsFintype L U hU hC
    Nat.card {x : L // (x : E) ∈ C} =
      ∑ q : quotientPoints L U C, Nat.card (fiberPoints L U hU C q) := by
  let := quotientPointsFintype L U hU hC
  let (q : quotientPoints L U C) := finite_fiberPoints L U hU hC q
  exact (Nat.card_congr (bodyPointsEquivSigma L U hU C)).trans Nat.card_sigma

/-- A bound on actual fibre counts multiplies by the count in the actual quotient lattice. -/
theorem card_body_le_mul_card_quotient {C : Set E} (hC : IsCompact C) (M : ℝ)
    (hbound : ∀ q : quotientPoints L U C, (Nat.card (fiberPoints L U hU C q) : ℝ) ≤ M) :
    (Nat.card {x : L // (x : E) ∈ C} : ℝ) ≤ M * Nat.card (quotientPoints L U C) := by
  let := quotientPointsFintype L U hU hC
  have hc : (Nat.card {x : L // (x : E) ∈ C} : ℝ) =
      ∑ q : quotientPoints L U C, (Nat.card (fiberPoints L U hU C q) : ℝ) := by
    exact_mod_cast card_body_eq_sum_fiber L U hU hC
  rw [hc]
  calc
    _ ≤ ∑ _q : quotientPoints L U C, M := Finset.sum_le_sum fun q _ => hbound q
    _ = _ := by simp [Nat.card_eq_fintype_card, mul_comm]

end ArakelovGeometry.GeometryOfNumbers.LatticeFiberCount

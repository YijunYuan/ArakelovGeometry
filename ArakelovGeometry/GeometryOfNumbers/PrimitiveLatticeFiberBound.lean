/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.GeometryOfNumbers.PrimitiveAffineSections
import ArakelovGeometry.GeometryOfNumbers.LatticeFiberCount

/-! # Actual lattice-fibre counting along a primitive vector -/

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.PrimitiveLatticeFiberBound

open Module MeasureTheory Set
open LatticeSubspaceBasis LatticeSubspaceCoordinates LatticePrimitiveVector LatticeFiberCount

attribute [local instance] Submodule.closed_of_finiteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (v : L) (hv : (v : E) ≠ 0)

/-- The primitive identity produces the actual integer parameterization of J. -/
def integerEquivIntersection
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E)) :
    ℤ ≃ intersectionAsSubmodule L (ℝ ∙ (v : E)) := by
  let f : ℤ → intersectionAsSubmodule L (ℝ ∙ (v : E)) := fun n =>
    ⟨⟨n • (v : E), ((ℝ ∙ (v : E)).restrictScalars ℤ).smul_mem n
      (Submodule.mem_span_singleton_self _)⟩, L.smul_mem n v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro m n h
    have hreal : (m : ℝ) = (n : ℝ) := smul_left_injective ℝ hv (by
      simpa only [f, Int.cast_smul_eq_zsmul] using
        congrArg (fun u : intersectionAsSubmodule L (ℝ ∙ (v : E)) => ((u : ℝ ∙ (v : E)) : E)) h)
    exact_mod_cast hreal
  · intro u
    have hu : ((u : ℝ ∙ (v : E)) : E) ∈
        L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ := ⟨u.property, u.val.property⟩
    rw [hprimitive] at hu
    obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hu
    exact ⟨n, Subtype.ext (Subtype.ext hn)⟩

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- The constructed integer equivalence sends n to the literal multiple nv. -/
theorem integerEquivIntersection_coe
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E)) (n : ℤ) :
    (((integerEquivIntersection L v hv hprimitive n : intersectionAsSubmodule L (ℝ ∙ (v : E))) :
      ℝ ∙ (v : E)) : E) = n • (v : E) := rfl

/-- Actual adapted coordinates separate into the original line inclusion and its affine shift. -/
theorem adaptedCoordinates_eq_add (u : ℝ ∙ (v : E)) (q : E ⧸ (ℝ ∙ (v : E))) :
    adaptedCoordinates L (ℝ ∙ (v : E)) (span_singleton_rational L v.property) (u, q) =
      (u : E) + adaptedCoordinates L (ℝ ∙ (v : E))
        (span_singleton_rational L v.property) (0, q) := by
  have hp : (u, q) = (u, 0) + (0, q) := by simp
  rw [hp, map_add, adaptedCoordinates_inl]

/-- The original affine integer expression is the actual adapted-coordinate expression. -/
theorem adaptedCoordinates_integer
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E))
    (n : ℤ) (q : E ⧸ (ℝ ∙ (v : E))) :
    adaptedCoordinates L (ℝ ∙ (v : E)) (span_singleton_rational L v.property)
      ((integerEquivIntersection L v hv hprimitive n : ℝ ∙ (v : E)), q) =
      (n : ℝ) • (v : E) + adaptedCoordinates L (ℝ ∙ (v : E))
        (span_singleton_rational L v.property) (0, q) := by
  rw [adaptedCoordinates_eq_add, integerEquivIntersection_coe,
    Int.cast_smul_eq_zsmul]

/-- The actual intersection-lattice fibre is the literal integer affine section,
including projected lattice points whose integer fibre is empty. -/
def fiberEquivIntegers
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E))
    {C : Set E} (q : quotientPoints L (ℝ ∙ (v : E)) C) :
    fiberPoints L (ℝ ∙ (v : E)) (span_singleton_rational L v.property) C q ≃
      {n : ℤ // (n : ℝ) • (v : E) + adaptedCoordinates L (ℝ ∙ (v : E))
        (span_singleton_rational L v.property) (0, (q.val : E ⧸ (ℝ ∙ (v : E)))) ∈ C} := by
  apply Equiv.symm
  refine Equiv.subtypeEquiv (integerEquivIntersection L v hv hprimitive) ?_
  intro n
  change _ ↔ adaptedCoordinates L (ℝ ∙ (v : E)) (span_singleton_rational L v.property)
    ((integerEquivIntersection L v hv hprimitive n : ℝ ∙ (v : E)),
      (q.val : E ⧸ (ℝ ∙ (v : E)))) ∈ C
  rw [adaptedCoordinates_integer]

section Measure

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (ℝ ∙ (v : E))] [BorelSpace (ℝ ∙ (v : E))]
  (ν : Measure (ℝ ∙ (v : E))) [ν.IsAddHaarMeasure]

include hv in
/-- The actual integer fibre count is bounded by the actual primitive normalized section. -/
theorem natCard_fiber_le_three_halves_section
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E))
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hvC : (v : E) ∈ C)
    (q : quotientPoints L (ℝ ∙ (v : E)) C) :
    (Nat.card (fiberPoints L (ℝ ∙ (v : E)) (span_singleton_rational L v.property) C q) : ℝ) ≤
      (3 / 2 : ℝ) * (latticeNormalizedMeasure
        (intersectionAsSubmodule L (ℝ ∙ (v : E))) ν
          ((ℝ ∙ (v : E)).subtype ⁻¹' C)).toReal := by
  rw [Nat.card_congr (fiberEquivIntegers L v hv hprimitive q)]
  exact PrimitiveAffineSections.natCard_affine_integer_le_three_halves_normalized
    L v hv ν hprimitive hcompact hconvex hsymm hvC _

include hv in
/-- The actual lattice body count satisfies the source three-halves counting step,
with all fibre bounds produced from the actual primitive line. -/
theorem card_body_le_three_halves_section_mul_quotient
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E))
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hvC : (v : E) ∈ C) :
    (Nat.card {x : L // (x : E) ∈ C} : ℝ) ≤
      ((3 / 2 : ℝ) * (latticeNormalizedMeasure
        (intersectionAsSubmodule L (ℝ ∙ (v : E))) ν
          ((ℝ ∙ (v : E)).subtype ⁻¹' C)).toReal) *
        Nat.card (quotientPoints L (ℝ ∙ (v : E)) C) := by
  apply card_body_le_mul_card_quotient L (ℝ ∙ (v : E))
    (span_singleton_rational L v.property) hcompact
  exact natCard_fiber_le_three_halves_section L v hv ν hprimitive hcompact hconvex hsymm hvC

end Measure

section PrimitiveChoice

variable [MeasurableSpace E] [BorelSpace E]

/-- The actual primitive-vector existence theorem supplies all line data for
the source counting step from a nonzero body lattice point. -/
theorem exists_primitive_card_body_bound {C : Set E} (hcompact : IsCompact C)
    (hconvex : Convex ℝ C) (hsymm : ∀ x ∈ C, -x ∈ C)
    (hnonzero : ∃ x ∈ C ∩ (L : Set E), x ≠ 0) :
    ∃ w : L, (w : E) ≠ 0 ∧ (w : E) ∈ C ∧
      L ⊓ (ℝ ∙ (w : E)).restrictScalars ℤ = ℤ ∙ (w : E) ∧
      (Nat.card {x : L // (x : E) ∈ C} : ℝ) ≤
        ((3 / 2 : ℝ) * (latticeNormalizedMeasure
          (intersectionAsSubmodule L (ℝ ∙ (w : E)))
          (Module.finBasis ℝ (ℝ ∙ (w : E))).addHaar
            ((ℝ ∙ (w : E)).subtype ⁻¹' C)).toReal) *
          Nat.card (quotientPoints L (ℝ ∙ (w : E)) C) := by
  obtain ⟨w, hw, hwC, hprimitive, _⟩ := exists_primitive_mem L hconvex hsymm hnonzero
  exact ⟨w, hw, hwC, hprimitive,
    card_body_le_three_halves_section_mul_quotient L w hw _ hprimitive
      hcompact hconvex hsymm hwC⟩

end PrimitiveChoice

end ArakelovGeometry.GeometryOfNumbers.PrimitiveLatticeFiberBound

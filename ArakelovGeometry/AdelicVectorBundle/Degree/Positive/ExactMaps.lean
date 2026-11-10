/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic
public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.ExactSequence
import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.ExactSequence
import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Isometry
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Positive degree in general norm-exact sequences

The actual source exact-sequence convention supplies algebraic exactness and
the prescribed completed pullback/pushforward end norms. The isometry producer
transports both positive degrees to the canonical kernel restriction/quotient,
where the proved all-subspace bounds apply. No numerical conclusion is a field
of the exactness predicate; zero ends and infinite capital discrepancy remain.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w w' w''

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  {G : Type w''} [AddCommGroup G] [Module K G] [FiniteDimensional K G]

/-- Source (4.36)'s lower bound for the original end space of any actual
norm-exact sequence, including the zero end. -/
theorem positiveDegree_left_le_of_isExactSequence
    (V : AdelicVectorBundle S E) (L : AdelicVectorBundle S F) (R : AdelicVectorBundle S G)
    (i : F →ₗ[K] E) (p : E →ₗ[K] G)
    (hx : NormFamily.IsExactSequence L.toNormFamily V.toNormFamily R.toNormFamily i p)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    L.positiveDegree hS hN ≤ V.positiveDegree hS hN := by
  rw [V.positiveDegree_exactSequence_left L R i p hx hS hN]
  exact V.positiveDegree_restrict_le hS hN p.ker

/-- Source (4.36)'s capital-discrepancy upper bound for arbitrary original
exact maps. The genuine capital discrepancy is allowed to be infinite. -/
theorem positiveDegree_le_add_majorantDiscrepancy_of_isExactSequence
    (V : AdelicVectorBundle S E) (L : AdelicVectorBundle S F) (R : AdelicVectorBundle S G)
    (i : F →ₗ[K] E) (p : E →ₗ[K] G)
    (hx : NormFamily.IsExactSequence L.toNormFamily V.toNormFamily R.toNormFamily i p)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.positiveDegree hS hN ≤ L.positiveDegree hS hN + R.positiveDegree hS hN +
      V.majorantDiscrepancy hN := by
  rw [V.positiveDegree_exactSequence_left L R i p hx hS hN,
    V.positiveDegree_exactSequence_right L R i p hx hS hN]
  exact V.positiveDegree_le_restrict_add_quotient_add_majorantDiscrepancy p.ker hS hN

/-- Source (4.37) for arbitrary exact maps, with the actual determinant
discrepancy and the original outside-infinity ultrametric hypothesis. -/
theorem positiveDegree_le_add_determinantDiscrepancy_of_isExactSequence
    (V : AdelicVectorBundle S E) (L : AdelicVectorBundle S F) (R : AdelicVectorBundle S G)
    (i : F →ₗ[K] E) (p : E →ₗ[K] G)
    (hx : NormFamily.IsExactSequence L.toNormFamily V.toNormFamily R.toNormFamily i p)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsUltrametric) :
    V.positiveDegree hS hN ≤ L.positiveDegree hS hN + R.positiveDegree hS hN +
      (V.determinantDiscrepancy : EReal) := by
  rw [V.positiveDegree_exactSequence_left L R i p hx hS hN,
    V.positiveDegree_exactSequence_right L R i p hx hS hN]
  exact V.positiveDegree_le_restrict_add_quotient_add_determinantDiscrepancy p.ker hS hN hV

/-- Actual Hermitian norm-exact sequences have the same upper bound with
zero discrepancy, on the original end spaces. -/
theorem positiveDegree_le_add_of_isExactSequence_isHermitian
    (V : AdelicVectorBundle S E) (L : AdelicVectorBundle S F) (R : AdelicVectorBundle S G)
    (i : F →ₗ[K] E) (p : E →ₗ[K] G)
    (hx : NormFamily.IsExactSequence L.toNormFamily V.toNormFamily R.toNormFamily i p)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    V.positiveDegree hS hN ≤ L.positiveDegree hS hN + R.positiveDegree hS hN := by
  rw [V.positiveDegree_exactSequence_left L R i p hx hS hN,
    V.positiveDegree_exactSequence_right L R i p hx hS hN]
  exact V.positiveDegree_le_restrict_add_quotient_of_isHermitian p.ker hS hN hV

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Dual degree and discrepancy preserved by completed isometries

The transpose of a rational completed-fibre isometry preserves the actual
completed dual norms. This identifies dual degrees and hence the actual
global determinant discrepancy, also in rank zero and at trivial valuations.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]



namespace AdelicVectorBundle

/-- Dual degrees agree under the actual contravariant completed isometry. -/
theorem degree_dual_eq_of_completed_isometry [S.IsProper]
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S) (e : V ≃ₗ[K] W)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    (V.dualOfNormMeasurability).degree =
      (W.dualOfNormMeasurability).degree := by
  symm
  apply degree_eq_of_completed_isometry _ _ e.dualMap
  intro ω z
  exact V.toNormFamily.dualEquiv_norm_eq_of_completed_isometry W.toNormFamily ω e (he ω) z

/-- Actual completed-fibre isometries preserve the global real determinant
discrepancy, without any original finite-place ultrametricity assumption. -/
theorem determinantDiscrepancy_eq_of_completed_isometry [S.IsProper]
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S) (e : V ≃ₗ[K] W)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.determinantDiscrepancy = W.determinantDiscrepancy := by
  rw [V.determinantDiscrepancy_eq_degree_add_degree_dual,
    W.determinantDiscrepancy_eq_degree_add_degree_dual,
    V.degree_eq_of_completed_isometry W e he,
    V.degree_dual_eq_of_completed_isometry W e he]

/-- Nested restriction preserves the actual global discrepancy under the
existing canonical rational subspace isomorphism. -/
theorem determinantDiscrepancy_restrict_restrict [S.IsProper]
    (V : AdelicVectorBundle S) (U W : Submodule K V) (h : U ≤ W)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    ((V.restrictOfNormMeasurability W).restrictOfNormMeasurability
      (U.comap W.subtype)).determinantDiscrepancy =
      (V.restrictOfNormMeasurability U).determinantDiscrepancy := by
  apply determinantDiscrepancy_eq_of_completed_isometry _ _
    (Submodule.comapSubtypeEquivOfLe h)
  intro ω z
  exact (V.toNormFamily.restrict_restrict_norm_eq U W h ω z).symm

/-- The total rational subspace has the actual ambient global discrepancy. -/
theorem determinantDiscrepancy_restrict_top [S.IsProper]
    (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.restrictOfNormMeasurability ⊤).determinantDiscrepancy =
      V.determinantDiscrepancy := by
  apply determinantDiscrepancy_eq_of_completed_isometry _ _ Submodule.topEquiv
  intro ω z
  exact (V.toNormFamily.restrict_top_norm_eq ω z).symm

end AdelicVectorBundle

end ArakelovGeometry

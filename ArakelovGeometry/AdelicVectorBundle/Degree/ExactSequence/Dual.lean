/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Basic
import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import ArakelovGeometry.AdelicVectorBundle.Dual.Restriction
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Exact-sequence degree bounds by duality

Canonical completed annihilator isometries identify the genuine dual
subquotient degrees. The lower degree inequality for the actual dual bundle
then gives the determinant-discrepancy bound and Hermitian degree additivity.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual quotient dual and the actual annihilator restriction have
equal degrees under their canonical rational isomorphism. -/
theorem degree_dual_quotient_eq_degree_restrict_annihilator [S.IsProper]
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    ((V.quotientOfNormMeasurability W).dualOfNormMeasurability).degree =
      ((V.dualOfNormMeasurability).restrictOfNormMeasurability W.dualAnnihilator).degree
        := by
  apply degree_eq_of_completed_isometry _ _ W.dualQuotEquivDualAnnihilator
  intro ω z
  exact (V.toNormFamily.quotient_dual_annihilator_norm_eq W ω z).symm

/-- Quotienting the actual dual by the rational annihilator gives the degree
of the actual restricted-space dual under the source local hypotheses. -/
theorem degree_dual_quotient_annihilator_eq_degree_dual_restrict [S.IsProper]
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametricAtFinitePlaces] :
    ((V.dualOfNormMeasurability).quotientOfNormMeasurability W.dualAnnihilator).degree
        =
      ((V.restrictOfNormMeasurability W).dualOfNormMeasurability).degree := by
  apply degree_eq_of_completed_isometry _ _ (Subspace.quotAnnihilatorEquiv W)
  intro ω z
  exact (V.toNormFamily.dual_quotient_annihilator_norm_eq W ω z).symm

/-- The actual degree minus determinant discrepancy is subadditive for the
restriction and quotient of an ultrametric-outside-infinity bundle. -/
theorem degree_sub_determinantDiscrepancy_le_restrict_add_quotient [S.IsProper]
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametricAtFinitePlaces] :
    V.degree - V.determinantDiscrepancy ≤
      ((V.restrictOfNormMeasurability W).degree -
        (V.restrictOfNormMeasurability W).determinantDiscrepancy) +
      ((V.quotientOfNormMeasurability W).degree -
        (V.quotientOfNormMeasurability W).determinantDiscrepancy) := by
  have h := (V.dualOfNormMeasurability).degree_restrict_add_degree_quotient_le
    W.dualAnnihilator
  rw [← V.degree_dual_quotient_eq_degree_restrict_annihilator W,
    V.degree_dual_quotient_annihilator_eq_degree_dual_restrict W] at h
  rw [V.determinantDiscrepancy_eq_degree_add_degree_dual,
    (V.restrictOfNormMeasurability W).determinantDiscrepancy_eq_degree_add_degree_dual,
    (V.quotientOfNormMeasurability W).determinantDiscrepancy_eq_degree_add_degree_dual]
  linarith

/-- Vanishing ambient Hermitian discrepancy and nonnegative end discrepancies
give the reverse of the ordinary two-step degree lower bound. -/
theorem degree_le_restrict_add_degree_quotient_of_isHermitian [S.IsProper]
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    V.degree ≤ (V.restrictOfNormMeasurability W).degree +
      (V.quotientOfNormMeasurability W).degree := by
  have h := V.degree_sub_determinantDiscrepancy_le_restrict_add_quotient W (hV := hV.1)
  have hz := V.determinantDiscrepancy_eq_zero_of_isHermitian
  have hR := (V.restrictOfNormMeasurability W).determinantDiscrepancy_nonneg
  have hQ := (V.quotientOfNormMeasurability W).determinantDiscrepancy_nonneg
  linarith

/-- Exact additivity of the genuine restriction and quotient degrees for
a Hermitian bundle, including zero ambient spaces and zero ends. -/
theorem degree_restrict_add_degree_quotient_eq_of_isHermitian [S.IsProper]
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    (V.restrictOfNormMeasurability W).degree +
      (V.quotientOfNormMeasurability W).degree = V.degree :=
  le_antisymm (V.degree_restrict_add_degree_quotient_le W)
    (V.degree_le_restrict_add_degree_quotient_of_isHermitian W)

end ArakelovGeometry.AdelicVectorBundle

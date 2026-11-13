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
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    ((V.quotientOfMeasurableBase W).dualOfMeasurableBase).degree =
      ((V.dualOfMeasurableBase).restrictOfMeasurableBase W.dualAnnihilator).degree
        := by
  apply degree_eq_of_completed_isometry _ _ W.dualQuotEquivDualAnnihilator
  intro ω z
  exact (V.toNormFamily.quotient_dual_annihilator_norm_eq W ω z).symm

/-- Quotienting the actual dual by the rational annihilator gives the degree
of the actual restricted-space dual under the source local hypotheses. -/
theorem degree_dual_quotient_annihilator_eq_degree_dual_restrict [S.IsProper]
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametric] :
    ((V.dualOfMeasurableBase).quotientOfMeasurableBase W.dualAnnihilator).degree
        =
      ((V.restrictOfMeasurableBase W).dualOfMeasurableBase).degree := by
  apply degree_eq_of_completed_isometry _ _ (Subspace.quotAnnihilatorEquiv W)
  intro ω z
  exact (V.toNormFamily.dual_quotient_annihilator_norm_eq W ω z).symm

/-- The actual degree minus determinant discrepancy is subadditive for the
restriction and quotient of an ultrametric-outside-infinity bundle. -/
theorem degree_sub_determinantDiscrepancy_le_restrict_add_quotient [S.IsProper]
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametric] :
    V.degree - V.determinantDiscrepancy ≤
      ((V.restrictOfMeasurableBase W).degree -
        (V.restrictOfMeasurableBase W).determinantDiscrepancy) +
      ((V.quotientOfMeasurableBase W).degree -
        (V.quotientOfMeasurableBase W).determinantDiscrepancy) := by
  have h := (V.dualOfMeasurableBase).degree_restrict_add_degree_quotient_le
    W.dualAnnihilator
  rw [← V.degree_dual_quotient_eq_degree_restrict_annihilator W,
    V.degree_dual_quotient_annihilator_eq_degree_dual_restrict W] at h
  rw [V.determinantDiscrepancy_eq_degree_add_degree_dual,
    (V.restrictOfMeasurableBase W).determinantDiscrepancy_eq_degree_add_degree_dual,
    (V.quotientOfMeasurableBase W).determinantDiscrepancy_eq_degree_add_degree_dual]
  linarith

/-- Vanishing ambient Hermitian discrepancy and nonnegative end discrepancies
give the reverse of the ordinary two-step degree lower bound. -/
theorem degree_le_restrict_add_degree_quotient_of_isHermitian [S.IsProper]
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    V.degree ≤ (V.restrictOfMeasurableBase W).degree +
      (V.quotientOfMeasurableBase W).degree := by
  have h := V.degree_sub_determinantDiscrepancy_le_restrict_add_quotient W (hV := hV.1)
  have hz := V.determinantDiscrepancy_eq_zero_of_isHermitian
  have hR := (V.restrictOfMeasurableBase W).determinantDiscrepancy_nonneg
  have hQ := (V.quotientOfMeasurableBase W).determinantDiscrepancy_nonneg
  linarith

/-- Exact additivity of the genuine restriction and quotient degrees for
a Hermitian bundle, including zero ambient spaces and zero ends. -/
theorem degree_restrict_add_degree_quotient_eq_of_isHermitian [S.IsProper]
    (V : AdelicVectorBundle S) (W : Submodule K V)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] :
    (V.restrictOfMeasurableBase W).degree +
      (V.quotientOfMeasurableBase W).degree = V.degree :=
  le_antisymm (V.degree_restrict_add_degree_quotient_le W)
    (V.degree_le_restrict_add_degree_quotient_of_isHermitian W)

end ArakelovGeometry.AdelicVectorBundle

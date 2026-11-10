/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeExactSequence
public import ArakelovGeometry.AdelicVectorBundle.DegreeIsometry
public import ArakelovGeometry.AdelicVectorBundle.Discrepancy
public import ArakelovGeometry.AdelicVectorBundle.DualRestriction

/-!
# Exact-sequence degree bounds by duality

Canonical completed annihilator isometries identify the genuine dual
subquotient degrees. The lower degree inequality for the actual dual bundle
then gives the determinant-discrepancy bound and Hermitian degree additivity.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual quotient dual and the actual annihilator restriction have
equal degrees under their canonical rational isomorphism. -/
theorem degree_dual_quotient_eq_degree_restrict_annihilator [S.IsProper]
    (V : AdelicVectorBundle S E) (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.quotientOfMeasurableBase W hS).dualOfMeasurableBase hS).degree hS hN =
      ((V.dualOfMeasurableBase hS).restrictOfMeasurableBase W.dualAnnihilator hS).degree
        hS hN := by
  apply degree_eq_of_completed_isometry _ _ W.dualQuotEquivDualAnnihilator hS hN
  intro ω z
  simp only [dualOfMeasurableBase_toNormFamily, quotientOfMeasurableBase_toNormFamily,
    restrictOfMeasurableBase_toNormFamily]
  exact (V.toNormFamily.quotient_dual_annihilator_norm_eq W ω z).symm

/-- Quotienting the actual dual by the rational annihilator gives the degree
of the actual restricted-space dual under the source local hypotheses. -/
theorem degree_dual_quotient_annihilator_eq_degree_dual_restrict [S.IsProper]
    (V : AdelicVectorBundle S E) (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsUltrametric) :
    ((V.dualOfMeasurableBase hS).quotientOfMeasurableBase W.dualAnnihilator hS).degree
        hS hN =
      ((V.restrictOfMeasurableBase W hS).dualOfMeasurableBase hS).degree hS hN := by
  apply degree_eq_of_completed_isometry _ _ (Subspace.quotAnnihilatorEquiv W) hS hN
  intro ω z
  simp only [dualOfMeasurableBase_toNormFamily, quotientOfMeasurableBase_toNormFamily,
    restrictOfMeasurableBase_toNormFamily]
  exact (V.toNormFamily.dual_quotient_annihilator_norm_eq hV hN W ω z).symm

/-- The actual degree minus determinant discrepancy is subadditive for the
restriction and quotient of an ultrametric-outside-infinity bundle. -/
theorem degree_sub_determinantDiscrepancy_le_restrict_add_quotient [S.IsProper]
    (V : AdelicVectorBundle S E) (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsUltrametric) :
    V.degree hS hN - V.determinantDiscrepancy ≤
      ((V.restrictOfMeasurableBase W hS).degree hS hN -
        (V.restrictOfMeasurableBase W hS).determinantDiscrepancy) +
      ((V.quotientOfMeasurableBase W hS).degree hS hN -
        (V.quotientOfMeasurableBase W hS).determinantDiscrepancy) := by
  have h := (V.dualOfMeasurableBase hS).degree_restrict_add_degree_quotient_le
    W.dualAnnihilator hS hN
  rw [← V.degree_dual_quotient_eq_degree_restrict_annihilator W hS hN,
    V.degree_dual_quotient_annihilator_eq_degree_dual_restrict W hS hN hV] at h
  rw [V.determinantDiscrepancy_eq_degree_add_degree_dual hS hN,
    (V.restrictOfMeasurableBase W hS).determinantDiscrepancy_eq_degree_add_degree_dual hS hN,
    (V.quotientOfMeasurableBase W hS).determinantDiscrepancy_eq_degree_add_degree_dual hS hN]
  linarith

/-- Vanishing ambient Hermitian discrepancy and nonnegative end discrepancies
give the reverse of the ordinary two-step degree lower bound. -/
theorem degree_le_restrict_add_degree_quotient_of_isHermitian [S.IsProper]
    (V : AdelicVectorBundle S E) (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    V.degree hS hN ≤ (V.restrictOfMeasurableBase W hS).degree hS hN +
      (V.quotientOfMeasurableBase W hS).degree hS hN := by
  have h := V.degree_sub_determinantDiscrepancy_le_restrict_add_quotient W hS hN hV.1
  have hz := V.determinantDiscrepancy_eq_zero_of_isHermitian hN hV
  have hR := (V.restrictOfMeasurableBase W hS).determinantDiscrepancy_nonneg
  have hQ := (V.quotientOfMeasurableBase W hS).determinantDiscrepancy_nonneg
  linarith

/-- Exact additivity of the genuine restriction and quotient degrees for
a Hermitian bundle, including zero ambient spaces and zero ends. -/
theorem degree_restrict_add_degree_quotient_eq_of_isHermitian [S.IsProper]
    (V : AdelicVectorBundle S E) (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    (V.restrictOfMeasurableBase W hS).degree hS hN +
      (V.quotientOfMeasurableBase W hS).degree hS hN = V.degree hS hN :=
  le_antisymm (V.degree_restrict_add_degree_quotient_le W hS hN)
    (V.degree_le_restrict_add_degree_quotient_of_isHermitian W hS hN hV)

end ArakelovGeometry.AdelicVectorBundle

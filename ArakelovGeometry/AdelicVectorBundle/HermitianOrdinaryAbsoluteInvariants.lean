/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.HermitianOrdinaryScalarExtensionComparison
import ArakelovGeometry.AdelicVectorBundle.HermitianClosedHNInvariants
import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants

/-!
# Actual ordinary absolute invariants of Hermitian bundles on a common-density base

Genuine ordinary native restrictions of original subspaces preserve degree and
mean. For perfect K, the actual closed Hermitian HN invariants and same-fibre
norm domination bound ordinary invariants above; ordinary monotonicity gives
the reverse bound. The canonical ordinary absolute definitions then agree
with the original positive degree and maximal slope in every rank.
-/

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianOrdinaryAbsoluteProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- The actual ordinary native restriction to an original extended subspace
preserves genuine degree. This does not require a perfect original field. -/
theorem degree_restrict_scalarExtension_of_isHermitian_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (A : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L) hcount hN
    (P.restrictOfMeasurableBase (A.baseChange L) hLS).degree hLS hLN =
      (V.restrictOfMeasurableBase A (Or.inr hcount)).degree (Or.inr hcount) hN := by
  intro hLN hLS P
  apply le_antisymm
  · exact (V.degree_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
      hcount hN hH (A.baseChange L)).trans_eq
        (V.degree_restrict_hermitianScalarExtension_of_isAlgClosed hcount hN hH A)
  · exact V.degree_le_restrict_scalarExtension hcount hN A

/-- Actual ordinary native original subspaces preserve real mean in every
rank by genuine degree equality and the canonical tensor subspace rank. -/
theorem slope_restrict_scalarExtension_of_isHermitian_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (A : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L) hcount hN
    (P.restrictOfMeasurableBase (A.baseChange L) hLS).slope hLS hLN =
      (V.restrictOfMeasurableBase A (Or.inr hcount)).slope (Or.inr hcount) hN := by
  intro hLN hLS P
  have hr : Module.finrank L (A.baseChange L) = Module.finrank K A :=
    (Submodule.toBaseChange.toLinearEquiv L A).finrank_eq.symm.trans Module.finrank_baseChange
  dsimp only [slope]
  rw [V.degree_restrict_scalarExtension_of_isHermitian_of_isAlgClosed hcount hN hH A, hr]

section PerfectBase

variable [PerfectField K]

/-- The actual ordinary extension to any algebraic closed field preserves
canonical positive degree over a perfect common-density original base. -/
theorem positiveDegree_scalarExtension_of_isHermitian_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L) hcount hN
    P.positiveDegree hLS hLN = V.positiveDegree (Or.inr hcount) hN := by
  intro hLN hLS P
  exact le_antisymm
    ((V.positiveDegree_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
      hcount hN hH).trans_eq
        (V.positiveDegree_hermitianScalarExtension_of_isAlgClosed hcount hN hH))
    (V.positiveDegree_le_scalarExtension_of_isAlgClosed hcount hN)

/-- The actual ordinary closed maximal slope is the original maximum over
a perfect common-density base, including the empty rank-zero supremum. -/
theorem maximalSlope_scalarExtension_of_isHermitian_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L) hcount hN
    P.maximalSlope hLS hLN = V.maximalSlope (Or.inr hcount) hN := by
  intro hLN hLS P
  exact le_antisymm
    ((V.maximalSlope_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
      hcount hN hH).trans_eq
        (V.maximalSlope_hermitianScalarExtension_of_isAlgClosed hcount hN hH))
    (V.maximalSlope_le_scalarExtension_of_isAlgClosed hcount hN)

/-- The canonical actual ordinary absolute positive degree equals original
positive degree for Hermitian bundles on a perfect common-density base. -/
theorem absolutePositiveDegree_eq_of_isHermitian
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    V.absolutePositiveDegree hcount hN = V.positiveDegree (Or.inr hcount) hN :=
  V.positiveDegree_scalarExtension_of_isHermitian_of_isAlgClosed
    (L := AlgebraicClosure K) hcount hN hH

/-- The canonical actual ordinary absolute maximum equals the genuine original
maximum for Hermitian bundles on a perfect common-density base, in all ranks. -/
theorem absoluteMaximalSlope_eq_of_isHermitian
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    V.absoluteMaximalSlope hcount hN = V.maximalSlope (Or.inr hcount) hN :=
  V.maximalSlope_scalarExtension_of_isHermitian_of_isAlgClosed
    (L := AlgebraicClosure K) hcount hN hH

end PerfectBase

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionHermitianComparison
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionHermitianDeterminantDegree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionSlopes

/-!
# Actual ordinary and Hermitian extension invariant comparison

The accepted same-completed-fibre Hermitian norm inequality dominates every
genuine ordinary native restricted degree and mean. Actual subspace suprema
then compare canonical positive degree and maximal slope in every rank.
-/

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianOrdinaryComparisonProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Every actual ordinary native restricted degree is at most its Hermitian
counterpart on the same actual target subspace and completed fibres. -/
theorem degree_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (U : Submodule L (L ⊗[K] E)) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L) hcount hN
    let H := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    (P.restrictOfMeasurableBase U hLS).degree hLS hLN ≤
      (H.restrictOfMeasurableBase U hLS).degree hLS hLN := by
  intro hLN hLS P H
  have hn : H.toNormFamily ≤ P.toNormFamily :=
    V.toNormFamily.hermitianScalarExtension_le_scalarExtension hN hLN hH
  exact degree_antitone (H.restrictOfMeasurableBase U hLS)
    (P.restrictOfMeasurableBase U hLS) hLS hLN (fun x z ↦ hn x _)

/-- Dividing genuine native restricted degree domination by the common rank
compares both real means, including the zero-rank convention. -/
theorem slope_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (U : Submodule L (L ⊗[K] E)) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L) hcount hN
    let H := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    (P.restrictOfMeasurableBase U hLS).slope hLS hLN ≤
      (H.restrictOfMeasurableBase U hLS).slope hLS hLN := by
  intro hLN hLS P H
  dsimp only [slope]
  exact div_le_div_of_nonneg_right
    (V.degree_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
      hcount hN hH U) (Nat.cast_nonneg _)

/-- The ordinary actual positive-degree supremum is bounded by the actual
Hermitian supremum, using every genuine native target restricted degree. -/
theorem positiveDegree_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L) hcount hN
    let H := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    P.positiveDegree hLS hLN ≤ H.positiveDegree hLS hLN := by
  intro hLN hLS P H
  apply P.positiveDegree_le hLS hLN
  intro U
  exact (EReal.coe_le_coe_iff.mpr
    (V.degree_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
      hcount hN hH U)).trans (H.degree_restrict_le_positiveDegree hLS hLN U)

/-- Every actual positive-rank ordinary mean is bounded by the same Hermitian
mean, hence the actual maximal-slope suprema are ordered in every rank. -/
theorem maximalSlope_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let P := V.scalarExtension (L := L) hcount hN
    let H := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    P.maximalSlope hLS hLN ≤ H.maximalSlope hLS hLN := by
  intro hLN hLS P H
  apply P.maximalSlope_le hLS hLN
  intro U hU
  exact (EReal.coe_le_coe_iff.mpr
    (V.slope_restrict_scalarExtension_le_hermitianScalarExtension_of_isAlgClosed
      hcount hN hH U)).trans (H.slope_restrict_le_maximalSlope U hU hLS hLN)

end ArakelovGeometry.AdelicVectorBundle

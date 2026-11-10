/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AlgebraicClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.HermitianScalarExtensionRestriction

/-!
# Actual canonical Hermitian degrees over an algebraic closure

The actual extended determinant-line degree producer applies to every algebraic
extension. Produced common countable density supplies the closed target's usual
vector degree. The genuine completed restriction isometry then identifies the
native restricted degrees and real means, including rank zero.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianClosedDegreeProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- The actual canonical degree of the Hermitian extension to an algebraically
closed algebraic field is the original degree. Target context is produced. -/
theorem degree_hermitianScalarExtension_of_isAlgClosed (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    W.degree hLS hLN = V.degree (Or.inr hcount) hN := by
  intro hLN hLS W
  have hd : (W.determinantOfMeasurableBase hLS hLN).lineDegree
      (W.determinantOfMeasurableBase_isLine hLS hLN) =
      (V.hermitianScalarExtensionDeterminant (L := L) (Or.inr hcount) hN hLN hH).lineDegree
        (V.hermitianScalarExtensionDeterminant_isLine (Or.inr hcount) hN hLN hH) := by
    apply lineDegree_eq_of_norm_rational_eq _ _ _ _ (LinearEquiv.refl L _)
    intro x z
    rfl
  exact hd.trans (V.lineDegree_hermitianScalarExtensionDeterminant
    (L := L) (Or.inr hcount) hN hLN hH)

/-- Genuine closed Hermitian extension preserves the ambient real mean slope,
including the existing real zero-rank convention. -/
theorem slope_hermitianScalarExtension_of_isAlgClosed (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    W.slope hLS hLN = V.slope (Or.inr hcount) hN := by
  intro hLN hLS W
  dsimp only [slope]
  rw [V.degree_hermitianScalarExtension_of_isAlgClosed hcount hN hH,
    Module.finrank_baseChange]

/-- Every native restriction after actual closed Hermitian extension has
the genuine original restricted degree, through the completed isometry. -/
theorem degree_restrict_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    (W.restrictOfMeasurableBase (U.baseChange L) hLS).degree hLS hLN =
      (V.restrictOfMeasurableBase U (Or.inr hcount)).degree (Or.inr hcount) hN := by
  intro hLN hLS W
  let R := V.restrictOfMeasurableBase U (Or.inr hcount)
  let Rext := R.hermitianScalarExtension (L := L) hcount hN hLN (hH.restrict U)
  have he : Rext.degree hLS hLN =
      (W.restrictOfMeasurableBase (U.baseChange L) hLS).degree hLS hLN :=
    Rext.degree_eq_of_completed_isometry _ (Submodule.toBaseChange.toLinearEquiv L U)
      hLS hLN (fun x z ↦ V.toNormFamily.hermitianScalarExtension_restrict_norm_eq
        hN hLN hH U x z)
  exact he.symm.trans
    (R.degree_hermitianScalarExtension_of_isAlgClosed hcount hN (hH.restrict U))

/-- Native closed Hermitian restriction preserves the genuine original mean
slope in every rank; no square root of minus one is assumed. -/
theorem slope_restrict_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    (W.restrictOfMeasurableBase (U.baseChange L) hLS).slope hLS hLN =
      (V.restrictOfMeasurableBase U (Or.inr hcount)).slope (Or.inr hcount) hN := by
  intro hLN hLS W
  have hr : Module.finrank L (U.baseChange L) = Module.finrank K U :=
    (Submodule.toBaseChange.toLinearEquiv L U).finrank_eq.symm.trans Module.finrank_baseChange
  dsimp only [slope]
  rw [V.degree_restrict_hermitianScalarExtension_of_isAlgClosed hcount hN hH U, hr]

end ArakelovGeometry.AdelicVectorBundle

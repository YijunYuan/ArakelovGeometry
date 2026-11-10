/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianClosedScalarExtensionDegree
public import ArakelovGeometry.AdelicVectorBundle.HermitianScalarExtensionQuotient

/-!
# Actual native quotient degree and mean under closed Hermitian extension

The genuine completed quotient isometry and the actual closed ambient degree
producer preserve both canonical native quotient invariants in every rank.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianClosedScalarQuotientProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Closed algebraic Hermitian extension preserves actual native quotient degree
via the genuine canonical quotient tensor isometry. -/
theorem degree_quotient_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    (W.quotientOfMeasurableBase (U.baseChange L) hLS).degree hLS hLN =
      (V.quotientOfMeasurableBase U (Or.inr hcount)).degree (Or.inr hcount) hN := by
  intro hLN hLS W
  let Q := V.quotientOfMeasurableBase U (Or.inr hcount)
  let Qext := Q.hermitianScalarExtension (L := L) hcount hN hLN (hH.quotient U)
  have he : Qext.degree hLS hLN =
      (W.quotientOfMeasurableBase (U.baseChange L) hLS).degree hLS hLN :=
    Qext.degree_eq_of_completed_isometry _ (tensorQuotientBaseChangeEquiv (L := L) U)
      hLS hLN (fun x z => V.toNormFamily.hermitianScalarExtension_quotient_norm_eq
        hN hLN hH U x z)
  exact he.symm.trans
    (Q.degree_hermitianScalarExtension_of_isAlgClosed hcount hN (hH.quotient U))

/-- Native quotient means are preserved in every rank by genuine degree
isometry and the canonical quotient tensor rank. -/
theorem slope_quotient_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    (W.quotientOfMeasurableBase (U.baseChange L) hLS).slope hLS hLN =
      (V.quotientOfMeasurableBase U (Or.inr hcount)).slope (Or.inr hcount) hN := by
  intro hLN hLS W
  have hr : Module.finrank L ((L ⊗[K] E) ⧸ U.baseChange L) =
      Module.finrank K (E ⧸ U) :=
    (tensorQuotientBaseChangeEquiv (L := L) U).finrank_eq.symm.trans Module.finrank_baseChange
  dsimp only [slope]
  rw [V.degree_quotient_hermitianScalarExtension_of_isAlgClosed hcount hN hH U, hr]

end ArakelovGeometry.AdelicVectorBundle

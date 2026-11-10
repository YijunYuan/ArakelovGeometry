/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Galois.Destabilizing
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Restriction
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual maximal slope under finite Galois Hermitian extension

The produced rational descent of the actual largest destabilizer and the
genuine restriction/base-change norm isometry preserve the maximal slope.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianGaloisMaximalSlopeProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Actual finite Galois Hermitian extension preserves maximal slope in
every rank, using the produced destabilizer descent and genuine restriction. -/
theorem maximalSlope_hermitianScalarExtension_of_finiteGalois
    [FiniteDimensional K L] [IsGalois K L] (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    W.maximalSlope hLS hLN = V.maximalSlope (Or.inr hcount) hN := by
  intro hLN hLS W
  have hdim (U : Submodule K E) :
      Module.finrank L (U.baseChange L) = Module.finrank K U :=
    (Submodule.toBaseChange.toLinearEquiv L U).finrank_eq.symm.trans Module.finrank_baseChange
  apply le_antisymm
  · by_cases hz : Module.finrank K E = 0
    · rw [W.maximalSlope_eq_bot_of_finrank_eq_zero hLS hLN
        (Module.finrank_baseChange.trans hz)]
      exact bot_le
    · have hr : 0 < Module.finrank K E := Nat.pos_of_ne_zero hz
      have hrL : 0 < Module.finrank L (L ⊗[K] E) := by
        rwa [Module.finrank_baseChange]
      let hLH := V.hermitianScalarExtension_isHermitian hcount hN hLN hH
      let D := W.destabilizingSubspace hLS hLN hLH hrL
      obtain ⟨U, hU, _⟩ :=
        V.existsUnique_baseChange_destabilizingSubspace_hermitianScalarExtension
          (L := L) hcount hN hH hr
      change U.baseChange L = D at hU
      have hpD : 0 < Module.finrank L D :=
        W.destabilizingSubspace_finrank_pos hLS hLN hLH hrL
      have hpU : 0 < Module.finrank K U := by
        rw [← hU, hdim] at hpD
        exact hpD
      calc
        W.maximalSlope hLS hLN =
            ((W.restrictOfMeasurableBase D hLS).slope hLS hLN : EReal) :=
          (W.slope_destabilizingSubspace_eq_maximalSlope hLS hLN hLH hrL).symm
        _ = ((V.restrictOfMeasurableBase U (Or.inr hcount)).slope
            (Or.inr hcount) hN : EReal) := by
          rw [← hU, V.slope_restrict_hermitianScalarExtension_of_finiteDimensional
            hcount hN hH U]
        _ ≤ V.maximalSlope (Or.inr hcount) hN :=
          V.slope_restrict_le_maximalSlope U hpU (Or.inr hcount) hN
  · apply V.maximalSlope_le (Or.inr hcount) hN
    intro U hU
    have hp : 0 < Module.finrank L (U.baseChange L) := (hdim U).symm ▸ hU
    have h := W.slope_restrict_le_maximalSlope (U.baseChange L) hp hLS hLN
    rwa [V.slope_restrict_hermitianScalarExtension_of_finiteDimensional hcount hN hH U] at h

end ArakelovGeometry.AdelicVectorBundle

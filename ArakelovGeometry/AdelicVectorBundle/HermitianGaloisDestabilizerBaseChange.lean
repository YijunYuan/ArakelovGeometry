/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.HermitianGaloisMaximalSlope

/-!
# The actual largest destabilizer under finite Galois Hermitian extension

Produced rational descent, actual maximal-slope equality and native restricted
mean preservation identify the actual extended destabilizer with the base change
of the actual original destabilizer.
-/

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianGaloisDestabilizerBaseChangeProper :
    (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- The actual largest destabilizer commutes with finite Galois Hermitian
extension. Its descent, coefficient stability and maximal slope are produced. -/
theorem destabilizingSubspace_baseChange_hermitianScalarExtension_of_finiteGalois
    [FiniteDimensional K L] [IsGalois K L] (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (hr : 0 < Module.finrank K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    let hLH := V.hermitianScalarExtension_isHermitian hcount hN hLN hH
    let hrL : 0 < Module.finrank L (L ⊗[K] E) :=
      (Module.finrank_baseChange (R := L) (S := K) (M' := E)).symm ▸ hr
    (V.destabilizingSubspace (Or.inr hcount) hN hH hr).baseChange L =
      W.destabilizingSubspace hLS hLN hLH hrL := by
  intro hLN hLS W hLH hrL
  let D := V.destabilizingSubspace (Or.inr hcount) hN hH hr
  let DL := W.destabilizingSubspace hLS hLN hLH hrL
  have hdim (U : Submodule K E) :
      Module.finrank L (U.baseChange L) = Module.finrank K U :=
    (Submodule.toBaseChange.toLinearEquiv L U).finrank_eq.symm.trans Module.finrank_baseChange
  have hmax := V.maximalSlope_hermitianScalarExtension_of_finiteGalois
    (L := L) hcount hN hH
  change W.maximalSlope hLS hLN = V.maximalSlope (Or.inr hcount) hN at hmax
  apply le_antisymm
  · apply W.le_destabilizingSubspace_of_slope_eq_maximalSlope hLS hLN hLH hrL
    · rw [hdim]
      exact V.destabilizingSubspace_finrank_pos (Or.inr hcount) hN hH hr
    · rw [V.slope_restrict_hermitianScalarExtension_of_finiteDimensional
        hcount hN hH D]
      exact (V.slope_destabilizingSubspace_eq_maximalSlope
        (Or.inr hcount) hN hH hr).trans hmax.symm
  · obtain ⟨U, hU, _⟩ :=
      V.existsUnique_baseChange_destabilizingSubspace_hermitianScalarExtension
        (L := L) hcount hN hH hr
    change U.baseChange L = DL at hU
    have hpU : 0 < Module.finrank K U := by
      have hp := W.destabilizingSubspace_finrank_pos hLS hLN hLH hrL
      change 0 < Module.finrank L DL at hp
      rw [← hU, hdim] at hp
      exact hp
    have hmU : ((V.restrictOfMeasurableBase U (Or.inr hcount)).slope
        (Or.inr hcount) hN : EReal) = V.maximalSlope (Or.inr hcount) hN := by
      calc
        _ = ((W.restrictOfMeasurableBase (U.baseChange L) hLS).slope hLS hLN : EReal) := by
          rw [V.slope_restrict_hermitianScalarExtension_of_finiteDimensional
            hcount hN hH U]
        _ = W.maximalSlope hLS hLN := by
          rw [hU]
          exact W.slope_destabilizingSubspace_eq_maximalSlope hLS hLN hLH hrL
        _ = V.maximalSlope (Or.inr hcount) hN := hmax
    have hUD : U ≤ D := V.le_destabilizingSubspace_of_slope_eq_maximalSlope
      (Or.inr hcount) hN hH hr U hpU hmU
    change DL ≤ D.baseChange L
    rw [← hU]
    exact Submodule.baseChange_mono L hUD

/-- A native original subspace extends to the actual target destabilizer
exactly when it is the actual original destabilizer. -/
theorem baseChange_eq_destabilizingSubspace_hermitianScalarExtension_iff_of_finiteGalois
    [FiniteDimensional K L] [IsGalois K L] (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (hr : 0 < Module.finrank K E)
    (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    let hLH := V.hermitianScalarExtension_isHermitian hcount hN hLN hH
    let hrL : 0 < Module.finrank L (L ⊗[K] E) :=
      (Module.finrank_baseChange (R := L) (S := K) (M' := E)).symm ▸ hr
    U.baseChange L = W.destabilizingSubspace hLS hLN hLH hrL ↔
      U = V.destabilizingSubspace (Or.inr hcount) hN hH hr := by
  intro hLN hLS W hLH hrL
  rw [← V.destabilizingSubspace_baseChange_hermitianScalarExtension_of_finiteGalois
    (L := L) hcount hN hH hr, Submodule.baseChange_inj]

end ArakelovGeometry.AdelicVectorBundle

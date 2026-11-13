/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Destabilizing
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.AlgebraicClosure.ScalarExtensionDegree
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Descent.InfiniteGalois
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Galois.Destabilizing
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual closed Hermitian largest-destabilizer descent and maximal slope

Proved closed coefficient stability and genuine infinite perfect-field descent
produce the actual rational ancestor. Native restricted means then preserve the
actual maximal slope in every rank.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L] [PerfectField K]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianClosedMaximalSlopeProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- The actual first destabilizer over a closed extension descends
uniquely, with coefficient stability proved rather than assumed. -/
theorem existsUnique_baseChange_destabilizingSubspace_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    let hrL : 0 < Module.finrank L (L ⊗[K] V) :=
      (Module.finrank_baseChange (R := L) (S := K) (M' := V)).symm ▸ hr
    ∃! U : Submodule K V, U.baseChange L = W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
        (hV := hLH) hrL := by
  intro hLN hLS W hLH hrL
  let D := W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL
  apply HermitianAbsoluteDescent.existsUnique_baseChange_eq_of_stable_of_isAlgClosed
  intro σ x hx
  have hfixed := V.destabilizingSubspace_hermitianScalarExtension_algEquiv_of_isAlgClosed
     hr σ
  change scalarExtensionSubspaceOrderIso σ D = D at hfixed
  change scalarExtensionSemilinearEquiv σ x ∈ D
  rw [← hfixed]
  exact ⟨x, hx, rfl⟩

/-- Actual closed Hermitian extension preserves maximal slope in
every rank, using the produced destabilizer descent and genuine restriction. -/
theorem maximalSlope_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    W.maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) = V.maximalSlope := by
  intro hLN hLS W
  have hdim (U : Submodule K V) :
      Module.finrank L (U.baseChange L) = Module.finrank K U :=
    (Submodule.toBaseChange.toLinearEquiv L U).finrank_eq.symm.trans Module.finrank_baseChange
  apply le_antisymm
  · by_cases hz : Module.finrank K V = 0
    · rw [W.maximalSlope_eq_bot_of_finrank_eq_zero (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
        (Module.finrank_baseChange.trans hz)]
      exact bot_le
    · have hr : 0 < Module.finrank K V := Nat.pos_of_ne_zero hz
      have hrL : 0 < Module.finrank L (L ⊗[K] V) := by
        rwa [Module.finrank_baseChange]
      let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
      let D := W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL
      obtain ⟨U, hU, _⟩ :=
        V.existsUnique_baseChange_destabilizingSubspace_hermitianScalarExtension_of_isAlgClosed
          (L := L) hr
      change U.baseChange L = D at hU
      have hpD : 0 < Module.finrank L D :=
        W.destabilizingSubspace_finrank_pos (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL
      have hpU : 0 < Module.finrank K U := by
        rw [← hU, hdim] at hpD
        exact hpD
      calc
        W.maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
            ((W.restrictOfMeasurableBase D (hS := ⟨hLS⟩)).slope (hS := ⟨hLS⟩)
                (hN := ⟨hLN⟩) : EReal) :=
          (W.slope_destabilizingSubspace_eq_maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
              (hV := hLH) hrL).symm
        _ = ((V.restrictOfMeasurableBase U).slope
            : EReal) := by
          rw [← hU, V.slope_restrict_hermitianScalarExtension_of_isAlgClosed
             U]
        _ ≤ V.maximalSlope :=
          V.slope_restrict_le_maximalSlope U hpU
  · apply V.maximalSlope_le
    intro U hU
    have hp : 0 < Module.finrank L (U.baseChange L) := (hdim U).symm ▸ hU
    have h := W.slope_restrict_le_maximalSlope (U.baseChange L) hp (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
    rwa [V.slope_restrict_hermitianScalarExtension_of_isAlgClosed U] at h

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Destabilizing
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.AlgebraicClosure.MaximalSlope
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.AlgebraicClosure.ScalarExtensionDegree
import Mathlib.CategoryTheory.Category.Init

/-!
# The actual largest destabilizer under closed Hermitian extension

Produced infinite rational descent and actual closed maximal-slope equality
identify the native original largest destabilizer with the actual target one.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L] [PerfectField K]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianClosedDestabilizerBaseChangeProper :
    (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- The actual largest destabilizer commutes with closed Hermitian
extension. Its descent, coefficient stability and maximal slope are produced. -/
theorem destabilizingSubspace_baseChange_hermitianScalarExtension_of_isAlgClosed
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
    (V.destabilizingSubspace hr).baseChange L =
      W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL := by
  intro hLN hLS W hLH hrL
  let D := V.destabilizingSubspace hr
  let DL := W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL
  have hdim (U : Submodule K V) :
      Module.finrank L (U.baseChange L) = Module.finrank K U :=
    (Submodule.toBaseChange.toLinearEquiv L U).finrank_eq.symm.trans Module.finrank_baseChange
  have hmax := V.maximalSlope_hermitianScalarExtension_of_isAlgClosed
    (L := L)
  change W.maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) = V.maximalSlope at hmax
  apply le_antisymm
  · apply W.le_destabilizingSubspace_of_slope_eq_maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
      (hV := hLH) hrL
    · rw [hdim]
      exact V.destabilizingSubspace_finrank_pos hr
    · rw [V.slope_restrict_hermitianScalarExtension_of_isAlgClosed
         D]
      exact (V.slope_destabilizingSubspace_eq_maximalSlope
        hr).trans hmax.symm
  · obtain ⟨U, hU, _⟩ :=
      V.existsUnique_baseChange_destabilizingSubspace_hermitianScalarExtension_of_isAlgClosed
        (L := L) hr
    change U.baseChange L = DL at hU
    have hpU : 0 < Module.finrank K U := by
      have hp := W.destabilizingSubspace_finrank_pos (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL
      change 0 < Module.finrank L DL at hp
      rw [← hU, hdim] at hp
      exact hp
    have hmU : ((V.restrictOfNormMeasurability U).slope
        : EReal) = V.maximalSlope := by
      calc
        _ = ((W.restrictOfNormMeasurability (U.baseChange L) (hS := ⟨hLS⟩)).slope (hS := ⟨hLS⟩)
            (hN := ⟨hLN⟩) : EReal) := by
          rw [V.slope_restrict_hermitianScalarExtension_of_isAlgClosed
             U]
        _ = W.maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := by
          rw [hU]
          exact W.slope_destabilizingSubspace_eq_maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
              (hV := hLH) hrL
        _ = V.maximalSlope := hmax
    have hUD : U ≤ D := V.le_destabilizingSubspace_of_slope_eq_maximalSlope
      hr U hpU hmU
    change DL ≤ D.baseChange L
    rw [← hU]
    exact Submodule.baseChange_mono L hUD

/-- A native original subspace extends to the actual target destabilizer
exactly when it is the actual original destabilizer. -/
theorem baseChange_eq_destabilizingSubspace_hermitianScalarExtension_iff_of_isAlgClosed
    (V : AdelicVectorBundle S)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (hr : 0 < Module.finrank K V)
    (U : Submodule K V) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    let hrL : 0 < Module.finrank L (L ⊗[K] V) :=
      (Module.finrank_baseChange (R := L) (S := K) (M' := V)).symm ▸ hr
    U.baseChange L = W.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) hrL ↔
      U = V.destabilizingSubspace hr := by
  intro hLN hLS W hLH hrL
  rw [← V.destabilizingSubspace_baseChange_hermitianScalarExtension_of_isAlgClosed
    (L := L) hr, Submodule.baseChange_inj]

end ArakelovGeometry.AdelicVectorBundle

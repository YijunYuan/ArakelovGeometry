/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Destabilizing
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Galois.MaximalSlope
import Mathlib.CategoryTheory.Category.Init

/-!
# Semistability under actual finite Galois Hermitian extension

The produced canonical mean and maximal slope equalities preserve and reflect
semistability. Source semistability retains positive rank; both zero bundles
therefore fail the predicate.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianGaloisSemistabilityProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Actual finite Hermitian scalar extension preserves the real mean slope
in every rank by the produced determinant degree and basis dimension equalities. -/
theorem slope_hermitianScalarExtension_of_finiteDimensional
    [FiniteDimensional K L] (V : AdelicVectorBundle S E)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    (V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)).slope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) =
      V.slope := by
  intro hLN hLS
  dsimp only [slope]
  rw [V.degree_hermitianScalarExtension_of_finiteDimensional (hL := ⟨hLN⟩),
    Module.finrank_baseChange]

/-- Source positive-rank semistability is preserved and reflected by actual
finite Galois Hermitian extension. Both rank-zero bundles fail this predicate. -/
theorem isMeanSlopeSemistable_hermitianScalarExtension_iff_of_finiteGalois
    [FiniteDimensional K L] [IsGalois K L] (V : AdelicVectorBundle S E)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    W.IsMeanSlopeSemistable (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) ↔ V.IsMeanSlopeSemistable := by
  intro hLN hLS W
  by_cases hr : 0 < Module.finrank K E
  · have hrL : 0 < Module.finrank L (L ⊗[K] E) := by
      rwa [Module.finrank_baseChange]
    rw [W.isMeanSlopeSemistable_iff_maximalSlope_eq_slope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) hrL,
      V.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hr,
      V.maximalSlope_hermitianScalarExtension_of_finiteGalois,
      V.slope_hermitianScalarExtension_of_finiteDimensional]
  · have hrL : ¬ 0 < Module.finrank L (L ⊗[K] E) := by
      rwa [Module.finrank_baseChange]
    constructor
    · intro hs
      exact False.elim (hrL hs.1)
    · intro hs
      exact False.elim (hr hs.1)

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.HermitianGaloisMaximalSlope

/-!
# Semistability under actual finite Galois Hermitian extension

The produced canonical mean and maximal slope equalities preserve and reflect
semistability. Source semistability retains positive rank; both zero bundles
therefore fail the predicate.
-/

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
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    (V.hermitianScalarExtension (L := L) hcount hN hLN hH).slope hLS hLN =
      V.slope (Or.inr hcount) hN := by
  intro hLN hLS
  dsimp only [slope]
  rw [V.degree_hermitianScalarExtension_of_finiteDimensional hcount hN hLN hH,
    Module.finrank_baseChange]

/-- Source positive-rank semistability is preserved and reflected by actual
finite Galois Hermitian extension. Both rank-zero bundles fail this predicate. -/
theorem isMeanSlopeSemistable_hermitianScalarExtension_iff_of_finiteGalois
    [FiniteDimensional K L] [IsGalois K L] (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    W.IsMeanSlopeSemistable hLS hLN ↔ V.IsMeanSlopeSemistable (Or.inr hcount) hN := by
  intro hLN hLS W
  by_cases hr : 0 < Module.finrank K E
  · have hrL : 0 < Module.finrank L (L ⊗[K] E) := by
      rwa [Module.finrank_baseChange]
    rw [W.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hLS hLN hrL,
      V.isMeanSlopeSemistable_iff_maximalSlope_eq_slope (Or.inr hcount) hN hr,
      V.maximalSlope_hermitianScalarExtension_of_finiteGalois hcount hN hH,
      V.slope_hermitianScalarExtension_of_finiteDimensional hcount hN hH]
  · have hrL : ¬ 0 < Module.finrank L (L ⊗[K] E) := by
      rwa [Module.finrank_baseChange]
    constructor
    · intro hs
      exact False.elim (hrL hs.1)
    · intro hs
      exact False.elim (hr hs.1)

end ArakelovGeometry.AdelicVectorBundle

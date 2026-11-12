/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Semistability
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.AlgebraicClosure.MaximalSlope
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.AlgebraicClosure.ScalarExtensionDegree
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Semistability
import Mathlib.CategoryTheory.Category.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Source and mean semistability under actual closed Hermitian extension

The source's positive-rank constant ordered-slope condition agrees with genuine
Hermitian mean semistability. Produced closed maximal and mean slope equalities
preserve and reflect both actual predicates, including their rank-zero failure.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w wL

section SourceMeanBridge

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type (max u w)}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual source semistability predicate and actual mean semistability
agree for a Hermitian bundle, preserving both positive-rank conditions. -/
theorem isSemistable_iff_isMeanSlopeSemistable_of_isHermitian
    (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    V.IsSemistable ↔ V.IsMeanSlopeSemistable := by
  by_cases hr : 0 < Module.finrank K E
  · rw [V.isSemistable_iff_modifiedSlope_eq_minimalSlope hr,
      V.modifiedSlope_eq_slope_of_isHermitian,
      V.isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian hr]
    exact eq_comm
  · constructor
    · intro hs
      exact False.elim (hr hs.1)
    · intro hs
      exact False.elim (hr hs.1)

end SourceMeanBridge

section ClosedMean

variable {K L E : Type*} [Field K] [Field L] [Algebra K L] [PerfectField K]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L] {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianClosedSemistabilityProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Source positive-rank semistability is preserved and reflected by actual
closed Hermitian extension. Both rank-zero bundles fail this predicate. -/
theorem isMeanSlopeSemistable_hermitianScalarExtension_iff_of_isAlgClosed
    (V : AdelicVectorBundle S E)
    [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    W.IsMeanSlopeSemistable (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) ↔ V.IsMeanSlopeSemistable := by
  intro hLN hLS W
  by_cases hr : 0 < Module.finrank K E
  · have hrL : 0 < Module.finrank L (L ⊗[K] E) := by
      rwa [Module.finrank_baseChange]
    rw [W.isMeanSlopeSemistable_iff_maximalSlope_eq_slope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) hrL,
      V.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hr,
      V.maximalSlope_hermitianScalarExtension_of_isAlgClosed,
      V.slope_hermitianScalarExtension_of_isAlgClosed]
  · have hrL : ¬ 0 < Module.finrank L (L ⊗[K] E) := by
      rwa [Module.finrank_baseChange]
    constructor
    · intro hs
      exact False.elim (hrL hs.1)
    · intro hs
      exact False.elim (hr hs.1)

end ClosedMean

section ClosedSource

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type (max u w)} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [PerfectField K]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L]

local instance hermitianClosedSourceSemistabilityProper :
    (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- The actual source semistability condition is preserved and reflected by
closed Hermitian extension of a perfect field, through the produced mean bridge. -/
theorem isSemistable_hermitianScalarExtension_iff_of_isAlgClosed
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    W.IsSemistable (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) ↔ V.IsSemistable := by
  intro hLN hLS W
  let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
  change W.toNormFamily.IsHermitian (hS := ⟨hLN⟩) at hLH
  rw [W.isSemistable_iff_isMeanSlopeSemistable_of_isHermitian (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
      (hH := hLH),
    V.isSemistable_iff_isMeanSlopeSemistable_of_isHermitian]
  exact V.isMeanSlopeSemistable_hermitianScalarExtension_iff_of_isAlgClosed

end ClosedSource

end ArakelovGeometry.AdelicVectorBundle

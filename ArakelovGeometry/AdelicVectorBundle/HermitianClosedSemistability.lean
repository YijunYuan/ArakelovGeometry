/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.HermitianClosedMaximalSlope
import ArakelovGeometry.AdelicVectorBundle.HermitianSemistability
import ArakelovGeometry.AdelicVectorBundle.GeneralHNSemistability

/-!
# Source and mean semistability under actual closed Hermitian extension

The source's positive-rank constant ordered-slope condition agrees with genuine
Hermitian mean semistability. Produced closed maximal and mean slope equalities
preserve and reflect both actual predicates, including their rank-zero failure.
-/

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
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    V.IsSemistable hS hN ↔ V.IsMeanSlopeSemistable hS hN := by
  by_cases hr : 0 < Module.finrank K E
  · rw [V.isSemistable_iff_modifiedSlope_eq_minimalSlope hS hN hr,
      V.modifiedSlope_eq_slope_of_isHermitian hS hN hH,
      V.isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian hS hN hH hr]
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
    (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    W.IsMeanSlopeSemistable hLS hLN ↔ V.IsMeanSlopeSemistable (Or.inr hcount) hN := by
  intro hLN hLS W
  by_cases hr : 0 < Module.finrank K E
  · have hrL : 0 < Module.finrank L (L ⊗[K] E) := by
      rwa [Module.finrank_baseChange]
    rw [W.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hLS hLN hrL,
      V.isMeanSlopeSemistable_iff_maximalSlope_eq_slope (Or.inr hcount) hN hr,
      V.maximalSlope_hermitianScalarExtension_of_isAlgClosed hcount hN hH,
      V.slope_hermitianScalarExtension_of_isAlgClosed hcount hN hH]
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
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    W.IsSemistable hLS hLN ↔ V.IsSemistable (Or.inr hcount) hN := by
  intro hLN hLS W
  let hLH := V.hermitianScalarExtension_isHermitian hcount hN hLN hH
  change W.toNormFamily.IsHermitian hLN at hLH
  rw [W.isSemistable_iff_isMeanSlopeSemistable_of_isHermitian hLS hLN hLH,
    V.isSemistable_iff_isMeanSlopeSemistable_of_isHermitian (Or.inr hcount) hN hH]
  exact V.isMeanSlopeSemistable_hermitianScalarExtension_iff_of_isAlgClosed hcount hN hH

end ClosedSource

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Transport

import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Isometry
import Mathlib.CategoryTheory.Category.Init

/-!
# Native determinant measurability and degree through actual place towers

The canonical measurable tower equivalence reflects fixed-vector norm
measurability. Actual determinant norms commute with this transport, and
measurable-determinant degree is preserved without target density hypotheses.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u wL wX
variable {K : Type u} [Field K] {S : AdelicStructure K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {X : Type wX} [AddCommGroup X] [Module L X]

namespace NormFamily

variable [FiniteDimensional L X]

/-- Source determinant measurability produces actual tower determinant
measurability, without a target measurability certificate. -/
theorem determinant_isMeasurable_towerPullback
    (ξ : NormFamily (S.algebraicExtension L) X) (F : IntermediateField K L)
    [hdet : ξ.determinant.IsMeasurable] :
    (ξ.towerPullback F).determinant.IsMeasurable := by
  rw [towerPullback_determinant]
  exact hdet.towerPullback F

omit [FiniteDimensional L X] in
/-- A completed isometry over a place tower descends determinant measurability. -/
theorem determinant_isMeasurable_of_tower_completed_isometry
    (F : IntermediateField K L)
    {X Y : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension L) X)
    (θ : NormFamily (S.algebraicExtension L) Y) (e : X ≃ₗ[L] Y)
    (he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (z : x.abv.Completion ⊗[L] X), θ.norm (scalarExtensionTowerPlace x)
        (e.toLinearMap.baseChange x.abv.Completion z) = η.norm x z)
    [hm : η.determinant.IsMeasurable] : θ.determinant.IsMeasurable := by
  have ht := η.determinant_isMeasurable_of_completed_isometry (θ.towerPullback F) e he
  rw [towerPullback_determinant] at ht
  exact (θ.determinant.isMeasurable_towerPullback_iff F).mp ht

end NormFamily
namespace AdelicVectorBundle
variable [FiniteDimensional L X]

section CompletedIsometry
omit [FiniteDimensional L X]

/-- Determinant degree is preserved by the measure-preserving tower map, with
measurability and Archimedean normalization supplied on both curves. -/
theorem degreeOfMeasurableDeterminant_towerPullback [S.IsProper]
    (V : AdelicVectorBundle (S.algebraicExtension L)) (F : IntermediateField K L)
    [hdetD : V.toNormFamily.determinant.IsMeasurable]
    [hdetT : (V.towerPullback F).toNormFamily.determinant.IsMeasurable]
    [hND : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hNT : ((S.algebraicExtension F).algebraicExtension L).IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
    (V.towerPullback F).degreeOfMeasurableDeterminant =
      V.degreeOfMeasurableDeterminant := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  change (V.towerPullback F).degreeOfMeasurableDeterminant =
    V.degreeOfMeasurableDeterminant
  let s := (V.determinant).lineGenerator (hV := (V.determinant_isLine))
  rw [degreeOfMeasurableDeterminant_eq_neg_integral (V.towerPullback F) s,
    degreeOfMeasurableDeterminant_eq_neg_integral V s]
  change -(∫ x, (V.toNormFamily.towerPullback F).determinant.logNorm s.val x
      ∂((S.algebraicExtension F).algebraicExtension L).v) =
    -(∫ x, V.toNormFamily.determinant.logNorm s.val x ∂(S.algebraicExtension L).v)
  rw [NormFamily.towerPullback_determinant, NormFamily.towerPullback_logNorm]
  exact congrArg (fun t : ℝ => -t)
    ((measurePreserving_scalarExtensionTowerPlace (S := S) F).integral_comp
      (AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurableEmbedding _)

/-- A completed isometry over a measure-preserving place tower preserves determinant degree. -/
theorem degreeOfMeasurableDeterminant_eq_of_tower_isometry [S.IsProper]
    (F : IntermediateField K L)
    (W : AdelicVectorBundle ((S.algebraicExtension F).algebraicExtension L))
    (R : AdelicVectorBundle (S.algebraicExtension L)) (e : W ≃ₗ[L] R)
    [hdetW : W.toNormFamily.determinant.IsMeasurable]
    [hdetR : R.toNormFamily.determinant.IsMeasurable]
    [hND : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hNT : ((S.algebraicExtension F).algebraicExtension L).IsArchimedeanNormalized]
    (he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (z : x.abv.Completion ⊗[L] W), R.toNormFamily.norm (scalarExtensionTowerPlace x)
        (e.toLinearMap.baseChange x.abv.Completion z) = W.toNormFamily.norm x z) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
    R.degreeOfMeasurableDeterminant =
      W.degreeOfMeasurableDeterminant := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  have hdetT : (R.towerPullback F).toNormFamily.determinant.IsMeasurable := by
    change (R.toNormFamily.towerPullback F).determinant.IsMeasurable
    rw [NormFamily.towerPullback_determinant]
    exact hdetR.towerPullback F
  exact (degreeOfMeasurableDeterminant_towerPullback R F (hdetT := hdetT)).symm.trans
    (W.degreeOfMeasurableDeterminant_eq_of_completed_isometry
      (R.towerPullback F) e he).symm

end CompletedIsometry

end AdelicVectorBundle
end ArakelovGeometry

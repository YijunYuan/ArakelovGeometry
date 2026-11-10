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
universe u v wL wX
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {X : Type wX} [AddCommGroup X] [Module L X]

namespace NormFamily

variable [FiniteDimensional L X]

/-- Source determinant measurability produces actual tower determinant
measurability, without a target measurability certificate. -/
theorem determinant_isMeasurable_towerPullback
    (ξ : NormFamily (S.algebraicExtension L) X) (F : IntermediateField K L)
    (hdet : ξ.determinant.IsMeasurable) :
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
    (hm : η.determinant.IsMeasurable) : θ.determinant.IsMeasurable := by
  have ht := η.determinant_isMeasurable_of_completed_isometry (θ.towerPullback F) e he hm
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
    {X : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    (V : AdelicVectorBundle (S.algebraicExtension L) X) (F : IntermediateField K L)
    (hdetD : V.toNormFamily.determinant.IsMeasurable)
    (hdetT : (V.towerPullback F).toNormFamily.determinant.IsMeasurable)
    (hND : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hNT : ∀ x ∈ ((S.algebraicExtension F).algebraicExtension L).Ωinf,
      IsRCLikeNormedField (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
    (V.towerPullback F).degreeOfMeasurableDeterminant hdetT hNT =
      V.degreeOfMeasurableDeterminant hdetD hND := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  change (V.towerPullback F).degreeOfMeasurableDeterminant hdetT hNT =
    V.degreeOfMeasurableDeterminant hdetD hND
  let s := (V.determinant hdetD hND).lineGenerator (V.determinant_isLine hdetD hND)
  rw [degreeOfMeasurableDeterminant_eq_neg_integral _ _ _ s,
    degreeOfMeasurableDeterminant_eq_neg_integral _ _ _ s]
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
    {X Y : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (W : AdelicVectorBundle ((S.algebraicExtension F).algebraicExtension L) X)
    (R : AdelicVectorBundle (S.algebraicExtension L) Y) (e : X ≃ₗ[L] Y)
    (hdetW : W.toNormFamily.determinant.IsMeasurable)
    (hdetR : R.toNormFamily.determinant.IsMeasurable)
    (hND : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hNT : ∀ x ∈ ((S.algebraicExtension F).algebraicExtension L).Ωinf,
      IsRCLikeNormedField (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion)
    (he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (z : x.abv.Completion ⊗[L] X), R.toNormFamily.norm (scalarExtensionTowerPlace x)
        (e.toLinearMap.baseChange x.abv.Completion z) = W.toNormFamily.norm x z) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
    R.degreeOfMeasurableDeterminant hdetR hND =
      W.degreeOfMeasurableDeterminant hdetW hNT := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  have hdetT : (R.towerPullback F).toNormFamily.determinant.IsMeasurable := by
    change (R.toNormFamily.towerPullback F).determinant.IsMeasurable
    rw [NormFamily.towerPullback_determinant]
    exact hdetR.towerPullback F
  exact (degreeOfMeasurableDeterminant_towerPullback R F hdetR hdetT hND hNT).symm.trans
    (W.degreeOfMeasurableDeterminant_eq_of_completed_isometry
      (R.towerPullback F) e hdetW hNT he).symm

end CompletedIsometry

end AdelicVectorBundle
end ArakelovGeometry

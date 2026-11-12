/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Absolute.CompatibleTower

import Mathlib.CategoryTheory.Category.Init

/-!
# Actual determinant degrees through compatible external towers

The genuine external tower place equivalence reflects rational norm
measurability. Actual determinant norms and logarithmic integrals commute with
its pullback, producing canonical determinant degree transport without target
place regularity.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v wL wM wX
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {M : Type wM} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [Algebra.IsAlgebraic L M] [Algebra.IsAlgebraic K M]
  {X : Type wX} [AddCommGroup X] [Module M X]

namespace NormFamily

/-- Rational norm measurability is reflected by the actual external tower
measurable equivalence, without a regularity premise on either place space. -/
theorem isMeasurable_compatibleTowerPullback_iff
    (ξ : NormFamily (S.algebraicExtension M) X) :
    (ξ.compatibleTowerPullback (L := L)).IsMeasurable ↔ ξ.IsMeasurable := by
  refine ⟨?_, fun h => h.compatibleTowerPullback⟩
  intro hξ
  constructor
  intro y
  let e := AdelicStructure.Algebraic.compatibleTowerMeasurableEquiv (L := L) (M := M) S
  have hn : (fun x : (S.algebraicExtension M).Ω =>
      ξ.norm x ((1 : x.abv.Completion) ⊗ₜ[M] y)) =
      (fun x : (S.algebraicExtension M).Ω =>
        (ξ.compatibleTowerPullback (L := L)).norm (e.symm x)
          ((1 : (e.symm x).abv.Completion) ⊗ₜ[M] y)) := by
    funext x
    change ξ.norm x _ = ξ.norm (e (e.symm x)) _
    exact (congrArg
      (fun t : (S.algebraicExtension M).Ω =>
        ξ.norm t ((1 : ((S.algebraicExtension M).ϕ t).Completion) ⊗ₜ[M] y))
      (e.apply_symm_apply x)).symm
  change Measurable (fun x : (S.algebraicExtension M).Ω =>
    ξ.norm x ((1 : x.abv.Completion) ⊗ₜ[M] y))
  rw [hn]
  exact (hξ y).comp e.symm.measurable

/-- Every rational log-norm integral follows the actual external tower
measure identity, with the total Bochner integral convention. -/
theorem integral_logNorm_compatibleTowerPullback
    (ξ : NormFamily (S.algebraicExtension M) X) (z : X) :
    (∫ x, (ξ.compatibleTowerPullback (L := L)).logNorm z x
      ∂((S.algebraicExtension L).algebraicExtension M).v) =
    ∫ x, ξ.logNorm z x ∂(S.algebraicExtension M).v := by
  rw [compatibleTowerPullback_logNorm]
  exact (AdelicStructure.Algebraic.measurePreserving_compatibleTowerMeasurableEquiv
    (L := L) S).integral_comp
      (AdelicStructure.Algebraic.compatibleTowerMeasurableEquiv (L := L) S).measurableEmbedding _

variable [FiniteDimensional M X]

/-- The actual determinant construction commutes with external tower pullback. -/
theorem compatibleTowerPullback_determinant (ξ : NormFamily (S.algebraicExtension M) X) :
    (ξ.compatibleTowerPullback (L := L)).determinant =
      ξ.determinant.compatibleTowerPullback (L := L) := by
  ext x z
  rfl

/-- Direct determinant measurability produces iterated determinant measurability. -/
theorem determinant_isMeasurable_compatibleTowerPullback
    (ξ : NormFamily (S.algebraicExtension M) X) [hdet : ξ.determinant.IsMeasurable] :
    (ξ.compatibleTowerPullback (L := L)).determinant.IsMeasurable := by
  rw [compatibleTowerPullback_determinant]
  exact hdet.compatibleTowerPullback

/-- Every actual determinant logarithm integral is preserved, in every rank. -/
theorem integral_determinant_logNorm_compatibleTowerPullback
    (ξ : NormFamily (S.algebraicExtension M) X)
    (t : ⋀[M]^(Module.finrank M X) X) :
    (∫ x, (ξ.compatibleTowerPullback (L := L)).determinant.logNorm t x
      ∂((S.algebraicExtension L).algebraicExtension M).v) =
    ∫ x, ξ.determinant.logNorm t x ∂(S.algebraicExtension M).v := by
  rw [compatibleTowerPullback_determinant]
  exact ξ.determinant.integral_logNorm_compatibleTowerPullback t

end NormFamily
namespace AdelicVectorBundle
variable [FiniteDimensional M X]

/-- The actual canonical determinant degree is transported through arbitrary
compatible external fields. Target measurability and normalization are produced. -/
theorem degreeOfMeasurableDeterminant_compatibleTowerPullback [S.IsProper]
    (V : AdelicVectorBundle (S.algebraicExtension M) X)
    [hdet : V.toNormFamily.determinant.IsMeasurable]
    [hN : S.IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension L) M
    (V.compatibleTowerPullback (L := L)).degreeOfMeasurableDeterminant
      (hdet := (V.toNormFamily.determinant_isMeasurable_compatibleTowerPullback))
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M)
        (hS := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩))⟩) =
      V.degreeOfMeasurableDeterminant
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := M))⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S M
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension L) M
  let hND := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := M)
  let hNT := AdelicStructure.isRCLikeNormedField_algebraicExtension
    (S := S.algebraicExtension L) (L := M)
    (hS := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩)
  have hdetT : (V.compatibleTowerPullback (L := L)).toNormFamily.determinant.IsMeasurable :=
    V.toNormFamily.determinant_isMeasurable_compatibleTowerPullback
  change (V.compatibleTowerPullback (L := L)).degreeOfMeasurableDeterminant (hdet := hdetT)
      (hN := ⟨hNT⟩) =
    V.degreeOfMeasurableDeterminant (hN := ⟨hND⟩)
  let s := (V.determinant (hS := ⟨hND⟩)).lineGenerator (hV := (V.determinant_isLine (hS := ⟨hND⟩)))
  rw [degreeOfMeasurableDeterminant_eq_neg_integral
      (V.compatibleTowerPullback (L := L)) (hdet := hdetT) (hN := ⟨hNT⟩) s,
    degreeOfMeasurableDeterminant_eq_neg_integral V (hN := ⟨hND⟩) s]
  exact congrArg (fun t : ℝ => -t)
    (V.toNormFamily.integral_determinant_logNorm_compatibleTowerPullback s.val)

end AdelicVectorBundle
end ArakelovGeometry

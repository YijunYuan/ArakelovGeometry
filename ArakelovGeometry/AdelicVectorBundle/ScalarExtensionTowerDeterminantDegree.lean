/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminant
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionFiniteStage
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTowerTransport

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

/-- Fixed-vector measurability is reflected by the genuine measurable tower
identification, without any regularity assumption on either place space. -/
theorem isMeasurable_towerPullback_iff (ξ : NormFamily (S.algebraicExtension L) X)
    (F : IntermediateField K L) : (ξ.towerPullback F).IsMeasurable ↔ ξ.IsMeasurable := by
  refine ⟨?_, fun h => h.towerPullback F⟩
  intro hξ y
  let e := AdelicStructure.Algebraic.towerMeasurableEquiv S F
  have hn : (fun x : (S.algebraicExtension L).Ω =>
      ξ.norm x ((1 : x.abv.Completion) ⊗ₜ[L] y)) =
      (fun x : (S.algebraicExtension L).Ω =>
        (ξ.towerPullback F).norm (e.symm x) ((1 : (e.symm x).abv.Completion) ⊗ₜ[L] y)) := by
    funext x
    change ξ.norm x _ = ξ.norm (e (e.symm x)) _
    exact (congrArg
      (fun t : (S.algebraicExtension L).Ω =>
        ξ.norm t ((1 : ((S.algebraicExtension L).ϕ t).Completion) ⊗ₜ[L] y))
      (e.apply_symm_apply x)).symm
  change Measurable (fun x : (S.algebraicExtension L).Ω =>
    ξ.norm x ((1 : x.abv.Completion) ⊗ₜ[L] y))
  rw [hn]
  exact (hξ y).comp e.symm.measurable

variable [FiniteDimensional L X]

/-- Source determinant measurability produces actual tower determinant
measurability, without a target measurability certificate. -/
theorem determinant_isMeasurable_towerPullback
    (ξ : NormFamily (S.algebraicExtension L) X) (F : IntermediateField K L)
    (hdet : ξ.determinant.IsMeasurable) :
    (ξ.towerPullback F).determinant.IsMeasurable := by
  rw [towerPullback_determinant]
  exact hdet.towerPullback F

end NormFamily
namespace AdelicVectorBundle
variable [FiniteDimensional L X]

/-- Measurable-determinant degree is transported through the genuine
measure-preserving tower. Pulled determinant measurability and both extension
normalizations are produced from the native determinant and original curve. -/
theorem degreeOfMeasurableDeterminant_towerPullback [S.IsProper]
    (V : AdelicVectorBundle (S.algebraicExtension L) X) (F : IntermediateField K L)
    (hdet : V.toNormFamily.determinant.IsMeasurable)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
    (V.towerPullback F).degreeOfMeasurableDeterminant
      (V.toNormFamily.determinant_isMeasurable_towerPullback F hdet)
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L)
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN)) =
      V.degreeOfMeasurableDeterminant hdet
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  let hND := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let hNT := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L)
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN)
  have hdetT : (V.towerPullback F).toNormFamily.determinant.IsMeasurable :=
    V.toNormFamily.determinant_isMeasurable_towerPullback F hdet
  change (V.towerPullback F).degreeOfMeasurableDeterminant hdetT hNT =
    V.degreeOfMeasurableDeterminant hdet hND
  let s := (V.determinant hdet hND).lineGenerator (V.determinant_isLine hdet hND)
  rw [degreeOfMeasurableDeterminant_eq_neg_integral (V.towerPullback F) hdetT hNT s,
    degreeOfMeasurableDeterminant_eq_neg_integral V hdet hND s]
  change -(∫ x, (V.toNormFamily.towerPullback F).determinant.logNorm s.val x
      ∂((S.algebraicExtension F).algebraicExtension L).v) =
    -(∫ x, V.toNormFamily.determinant.logNorm s.val x ∂(S.algebraicExtension L).v)
  rw [NormFamily.towerPullback_determinant, NormFamily.towerPullback_logNorm]
  exact congrArg (fun t : ℝ => -t)
    ((measurePreserving_scalarExtensionTowerPlace (S := S) F).integral_comp
      (AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurableEmbedding _)

end AdelicVectorBundle
end ArakelovGeometry

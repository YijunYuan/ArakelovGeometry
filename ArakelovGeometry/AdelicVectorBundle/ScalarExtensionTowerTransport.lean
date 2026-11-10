/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTower
import ArakelovGeometry.AdelicVectorBundle.Degree
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Tower

/-!
# Actual bundle and degree transport through the canonical tower equivalence

The norm-family tower map is the existing measure-preserving algebraic tower
identification. Pulling back its actual completed norms transports regularity
and degree without replacing either adelic curve or its parameter sigma algebra.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module L E]

/-- The completed-norm tower place is the canonical measurable tower map. -/
theorem scalarExtensionTowerPlace_eq_towerMeasurableEquiv (F : IntermediateField K L)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L) :
    scalarExtensionTowerPlace x = AdelicStructure.Algebraic.towerMeasurableEquiv S F x := rfl

/-- The actual completed-norm tower map preserves the extension measure. -/
theorem measurePreserving_scalarExtensionTowerPlace (F : IntermediateField K L) :
    @MeasurePreserving ((S.algebraicExtension F).algebraicExtension L).Ω
      (S.algebraicExtension L).Ω
      ((S.algebraicExtension F).algebraicExtension L).instMeasurableSpaceΩ
      (S.algebraicExtension L).instMeasurableSpaceΩ
      (scalarExtensionTowerPlace (S := S) (L := F) (M := L))
      ((S.algebraicExtension F).algebraicExtension L).v (S.algebraicExtension L).v := by
  change MeasurePreserving (AdelicStructure.Algebraic.towerMeasurableEquiv S F) _ _
  exact ⟨(AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurable,
    AdelicStructure.Algebraic.map_measure_towerMeasurableEquiv S F⟩

/-- An integrable upper envelope transports through a measure-preserving map. -/
theorem HasIntegrableUpperBound.comp_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : β → ℝ} {g : α → β}
    (hf : HasIntegrableUpperBound f ν) (hg : MeasurePreserving g μ ν) :
    HasIntegrableUpperBound (f ∘ g) μ := by
  obtain ⟨A, hA, hfA⟩ := hf
  exact ⟨A ∘ g, hg.integrable_comp_of_integrable hA, hg.quasiMeasurePreserving.ae hfA⟩

namespace NormFamily

/-- The actual completed norm family transported along the canonical tower map. -/
def towerPullback (ξ : NormFamily (S.algebraicExtension L) E) (F : IntermediateField K L) :
    NormFamily ((S.algebraicExtension F).algebraicExtension L) E where
  norm x := ξ.norm (scalarExtensionTowerPlace x)
  norm_eq_zero_iff x := ξ.norm_eq_zero_iff (scalarExtensionTowerPlace x)

@[simp]
theorem towerPullback_norm (ξ : NormFamily (S.algebraicExtension L) E)
    (F : IntermediateField K L)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (z : x.abv.Completion ⊗[L] E) :
    (ξ.towerPullback F).norm x z = ξ.norm (scalarExtensionTowerPlace x) z := rfl

/-- Rational logarithmic norms are exactly composition with the tower map. -/
@[simp]
theorem towerPullback_logNorm (ξ : NormFamily (S.algebraicExtension L) E)
    (F : IntermediateField K L) (z : E) :
    (ξ.towerPullback F).logNorm z =
      ξ.logNorm z ∘ AdelicStructure.Algebraic.towerMeasurableEquiv S F := rfl

variable [FiniteDimensional L E]

/-- Actual completed operator duals commute with canonical tower transport. -/
@[simp]
theorem towerPullback_dual (ξ : NormFamily (S.algebraicExtension L) E)
    (F : IntermediateField K L) :
    (ξ.towerPullback F).dual = ξ.dual.towerPullback F := by
  ext x z
  rfl

/-- Actual determinant quotient norms commute with canonical tower transport. -/
@[simp]
theorem towerPullback_determinant (ξ : NormFamily (S.algebraicExtension L) E)
    (F : IntermediateField K L) :
    (ξ.towerPullback F).determinant = ξ.determinant.towerPullback F := by
  ext x z
  rfl

omit [FiniteDimensional L E] in
/-- Fixed-vector norm measurability is preserved by the actual tower map. -/
theorem IsMeasurable.towerPullback {ξ : NormFamily (S.algebraicExtension L) E}
    (hξ : ξ.IsMeasurable) (F : IntermediateField K L) :
    (ξ.towerPullback F).IsMeasurable := by
  intro z
  exact (hξ z).comp (AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurable

omit [FiniteDimensional L E] in
/-- Integrable envelopes pull back through the actual measure-preserving map. -/
theorem IsUpperDominated.towerPullback {ξ : NormFamily (S.algebraicExtension L) E}
    (hξ : ξ.IsUpperDominated) (F : IntermediateField K L) :
    (ξ.towerPullback F).IsUpperDominated := by
  intro z hz
  rw [towerPullback_logNorm]
  exact (hξ z hz).comp_measurePreserving
    (measurePreserving_scalarExtensionTowerPlace (S := S) F)

/-- Both actual dual upper envelopes are transported, proving domination. -/
theorem IsDominated.towerPullback {ξ : NormFamily (S.algebraicExtension L) E}
    (hξ : ξ.IsDominated) (F : IntermediateField K L) :
    (ξ.towerPullback F).IsDominated := by
  refine ⟨hξ.1.towerPullback F, ?_⟩
  rw [towerPullback_dual]
  exact hξ.2.towerPullback F

end NormFamily

namespace AdelicVectorBundle

variable [FiniteDimensional L E]

/-- The actual tower pullback preserves both measurability clauses and domination. -/
def towerPullback (V : AdelicVectorBundle (S.algebraicExtension L) E)
    (F : IntermediateField K L) :
    AdelicVectorBundle ((S.algebraicExtension F).algebraicExtension L) E where
  toNormFamily := V.toNormFamily.towerPullback F
  isMeasurable := V.isMeasurable.towerPullback F
  dual_isMeasurable := by
    rw [NormFamily.towerPullback_dual]
    exact V.dual_isMeasurable.towerPullback F
  isDominated := V.isDominated.towerPullback F

@[simp]
theorem towerPullback_toNormFamily (V : AdelicVectorBundle (S.algebraicExtension L) E)
    (F : IntermediateField K L) :
    (V.towerPullback F).toNormFamily = V.toNormFamily.towerPullback F := rfl

/-- Tower transport preserves the same one-dimensional vector space. -/
theorem isLine_towerPullback (V : AdelicVectorBundle (S.algebraicExtension L) E)
    (F : IntermediateField K L) (hV : V.IsLine) : (V.towerPullback F).IsLine := hV

/-- Actual line degree is unchanged by the measure-preserving tower equivalence. -/
theorem lineDegree_towerPullback [S.IsProper]
    (V : AdelicVectorBundle (S.algebraicExtension L) E)
    (F : IntermediateField K L) (hV : V.IsLine) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
    (V.towerPullback F).lineDegree (V.isLine_towerPullback F hV) = V.lineDegree hV := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  change (V.towerPullback F).lineDegree (V.isLine_towerPullback F hV) = V.lineDegree hV
  let s := V.lineGenerator hV
  rw [lineDegree_eq_neg_integral _ _ s, lineDegree_eq_neg_integral _ _ s]
  change -(∫ x, V.toNormFamily.logNorm s.val
      (AdelicStructure.Algebraic.towerMeasurableEquiv S F x)
      ∂((S.algebraicExtension F).algebraicExtension L).v) =
    -(∫ x, V.toNormFamily.logNorm s.val x ∂(S.algebraicExtension L).v)
  exact congrArg (fun t : ℝ => -t)
    ((measurePreserving_scalarExtensionTowerPlace (S := S) F).integral_comp
      (AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurableEmbedding _)

/-- Actual vector degrees are unchanged, using the canonical determinant norms. -/
theorem degree_towerPullback [S.IsProper]
    (V : AdelicVectorBundle (S.algebraicExtension L) E)
    (F : IntermediateField K L)
    (hD : DiscreteMeasurableSpace (S.algebraicExtension L).Ω ∨
      (S.algebraicExtension L).HasCommonCountableDenseSubfield)
    (hT : DiscreteMeasurableSpace ((S.algebraicExtension F).algebraicExtension L).Ω ∨
      ((S.algebraicExtension F).algebraicExtension L).HasCommonCountableDenseSubfield)
    (hND : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hNT : ∀ x ∈ ((S.algebraicExtension F).algebraicExtension L).Ωinf,
      IsRCLikeNormedField (((S.algebraicExtension F).algebraicExtension L).ϕ x).Completion) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
    (V.towerPullback F).degree hT hNT = V.degree hD hND := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  change (V.towerPullback F).degree hT hNT = V.degree hD hND
  let s := (V.determinantOfMeasurableBase hD hND).lineGenerator
    (V.determinantOfMeasurableBase_isLine hD hND)
  rw [degree_eq_neg_integral _ hT hNT s, degree_eq_neg_integral _ hD hND s]
  change -(∫ x, (V.toNormFamily.towerPullback F).determinant.logNorm s.val x
      ∂((S.algebraicExtension F).algebraicExtension L).v) =
    -(∫ x, V.toNormFamily.determinant.logNorm s.val x ∂(S.algebraicExtension L).v)
  rw [NormFamily.towerPullback_determinant, NormFamily.towerPullback_logNorm]
  exact congrArg (fun t : ℝ => -t)
    ((measurePreserving_scalarExtensionTowerPlace (S := S) F).integral_comp
      (AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurableEmbedding _)

end AdelicVectorBundle
end ArakelovGeometry

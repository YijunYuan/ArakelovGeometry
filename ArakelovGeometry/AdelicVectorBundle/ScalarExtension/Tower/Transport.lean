/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerBasic
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerPlace
public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Tower
import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual bundle and degree transport through the canonical tower equivalence

The norm-family tower map is the existing measure-preserving algebraic tower
identification. Pulling back its actual completed norms transports regularity
and degree without replacing either adelic curve or its parameter sigma algebra.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

universe u wL wE
variable {K : Type u} [Field K] {S : AdelicStructure K}
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
  constructor
  intro z
  exact (hξ z).comp (AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurable

omit [FiniteDimensional L E] in
/-- Integrable envelopes pull back through the actual measure-preserving map. -/
theorem IsUpperDominated.towerPullback {ξ : NormFamily (S.algebraicExtension L) E}
    (hξ : ξ.IsUpperDominated) (F : IntermediateField K L) :
    (ξ.towerPullback F).IsUpperDominated := by
  constructor
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

section CompletedIsometry
omit [FiniteDimensional L E]

section
variable {X : Type*} [AddCommGroup X] [Module L X]

/-- Fixed-vector measurability is reflected by the genuine measurable tower
identification, without any regularity assumption on either place space. -/
theorem isMeasurable_towerPullback_iff (ξ : NormFamily (S.algebraicExtension L) X)
    (F : IntermediateField K L) : (ξ.towerPullback F).IsMeasurable ↔ ξ.IsMeasurable := by
  refine ⟨?_, fun h => h.towerPullback F⟩
  intro hξ
  constructor
  intro y
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

end

/-- Actual completed isometry transports dual norms across the canonical
place tower. The proof uses the genuine completed dual pairing and every vector. -/
private theorem dual_norm_eq_of_tower_completed_isometry
    (F : AdelicStructure.FiniteIntermediateField K L)
    {X Y : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension L) X)
    (θ : NormFamily (S.algebraicExtension L) Y) (e : X ≃ₗ[L] Y)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (he : ∀ t, θ.norm (scalarExtensionTowerPlace x)
      (e.toLinearMap.baseChange x.abv.Completion t) = η.norm x t)
    (z : x.abv.Completion ⊗[L] Module.Dual L Y) :
    η.dual.norm x (e.toLinearMap.dualMap.baseChange x.abv.Completion z) =
      θ.dual.norm (scalarExtensionTowerPlace x) z := by
  have hm (t : x.abv.Completion ⊗[L] X) : η.norm x t =
      θ.norm (scalarExtensionTowerPlace x) (e.toLinearMap.baseChange x.abv.Completion t) :=
    (he t).symm
  apply le_antisymm
  · apply η.dual_norm_le x _ (θ.dual.norm_nonneg (scalarExtensionTowerPlace x) z)
    intro t
    change x.abv.Completion ⊗[L] X at t
    change ‖dualBaseChangeEquiv L x.abv.Completion X
        (e.toLinearMap.dualMap.baseChange x.abv.Completion z) t‖ ≤
      θ.dual.norm (scalarExtensionTowerPlace x) z * η.norm x t
    rw [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply, hm]
    exact θ.norm_dual_apply_le (scalarExtensionTowerPlace x) z _
  · apply θ.dual_norm_le (scalarExtensionTowerPlace x) z (η.dual.norm_nonneg x _)
    intro y
    change x.abv.Completion ⊗[L] Y at y
    obtain ⟨t, rfl⟩ := (e.baseChange L x.abv.Completion _ _).surjective y
    change ‖dualBaseChangeEquiv L x.abv.Completion Y z
        (e.toLinearMap.baseChange x.abv.Completion t)‖ ≤
      η.dual.norm x (e.toLinearMap.dualMap.baseChange x.abv.Completion z) *
        θ.norm (scalarExtensionTowerPlace x) (e.toLinearMap.baseChange x.abv.Completion t)
    have h := η.norm_dual_apply_le x
      (e.toLinearMap.dualMap.baseChange x.abv.Completion z) t
    change ‖dualBaseChangeEquiv L x.abv.Completion X
        (e.toLinearMap.dualMap.baseChange x.abv.Completion z) t‖ ≤
      η.dual.norm x (e.toLinearMap.dualMap.baseChange x.abv.Completion z) * η.norm x t at h
    rw [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply, hm] at h
    exact h

/-- Measurability of dual norms descends through the measurable tower equivalence. -/
theorem IsMeasurable.dual_of_tower_completed_isometry
    (F : AdelicStructure.FiniteIntermediateField K L)
    {X Y : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension L) X)
    (θ : NormFamily (S.algebraicExtension L) Y) (e : X ≃ₗ[L] Y)
    (he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (z : x.abv.Completion ⊗[L] X), θ.norm (scalarExtensionTowerPlace x)
        (e.toLinearMap.baseChange x.abv.Completion z) = η.norm x z)
    (hm : η.dual.IsMeasurable) : θ.dual.IsMeasurable := by
  constructor
  intro ℓ
  let τ := (AdelicStructure.Algebraic.towerMeasurableEquiv S F.toIntermediateField).symm
  have hnorm : (fun x : (S.algebraicExtension L).Ω =>
      θ.dual.norm x ((1 : x.abv.Completion) ⊗ₜ[L] ℓ)) =
      (fun x : (S.algebraicExtension L).Ω =>
        η.dual.norm (τ x) ((1 : (τ x).abv.Completion) ⊗ₜ[L] e.dualMap ℓ)) := by
    funext x
    have h := dual_norm_eq_of_tower_completed_isometry F η θ e (τ x) (he (τ x))
      ((1 : x.abv.Completion) ⊗ₜ[L] ℓ)
    change η.dual.norm (τ x)
      (e.toLinearMap.dualMap.baseChange (τ x).abv.Completion
        ((1 : (τ x).abv.Completion) ⊗ₜ[L] ℓ)) =
      θ.dual.norm x ((1 : x.abv.Completion) ⊗ₜ[L] ℓ) at h
    rw [LinearMap.baseChange_tmul] at h
    exact h.symm
  change Measurable (fun x : (S.algebraicExtension L).Ω =>
    θ.dual.norm x ((1 : x.abv.Completion) ⊗ₜ[L] ℓ))
  rw [hnorm]
  exact (hm (e.dualMap ℓ)).comp τ.measurable

end CompletedIsometry

end NormFamily

namespace AdelicVectorBundle

variable [FiniteDimensional L E]

/-- The actual tower pullback preserves both measurability clauses and domination. -/
abbrev towerPullback (V : AdelicVectorBundle (S.algebraicExtension L))
    (F : IntermediateField K L) :
    AdelicVectorBundle ((S.algebraicExtension F).algebraicExtension L) where
  carrier := V
  toNormFamily := V.toNormFamily.towerPullback F
  toIsAdelic := {
    isMeasurable := V.isMeasurable.towerPullback F
    dual_isMeasurable := by
      rw [NormFamily.towerPullback_dual]
      exact V.dual_isMeasurable.towerPullback F
    isDominated := V.isDominated.towerPullback F
  }

@[simp]
theorem towerPullback_toNormFamily (V : AdelicVectorBundle (S.algebraicExtension L))
    (F : IntermediateField K L) :
    (V.towerPullback F).toNormFamily = V.toNormFamily.towerPullback F := rfl

/-- Tower transport preserves the same one-dimensional vector space. -/
instance isLine_towerPullback (V : AdelicVectorBundle (S.algebraicExtension L))
    (F : IntermediateField K L) [hV : V.IsLine] : (V.towerPullback F).IsLine := ⟨hV.rank_eq_one⟩

/-- Actual line degree is unchanged by the measure-preserving tower equivalence. -/
theorem lineDegree_towerPullback [S.IsProper]
    (V : AdelicVectorBundle (S.algebraicExtension L))
    (F : IntermediateField K L) [hV : V.IsLine] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
    (V.towerPullback F).lineDegree (hV := (V.isLine_towerPullback F)) = V.lineDegree := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  change (V.towerPullback F).lineDegree (hV := (V.isLine_towerPullback F)) = V.lineDegree
  let s := V.lineGenerator
  rw [lineDegree_eq_neg_integral (V.towerPullback F) s,
    lineDegree_eq_neg_integral V s]
  change -(∫ x, V.toNormFamily.logNorm s.val
      (AdelicStructure.Algebraic.towerMeasurableEquiv S F x)
      ∂((S.algebraicExtension F).algebraicExtension L).v) =
    -(∫ x, V.toNormFamily.logNorm s.val x ∂(S.algebraicExtension L).v)
  exact congrArg (fun t : ℝ => -t)
    ((measurePreserving_scalarExtensionTowerPlace (S := S) F).integral_comp
      (AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurableEmbedding _)

/-- Actual vector degrees are unchanged, using the canonical determinant norms. -/
theorem degree_towerPullback [S.IsProper]
    (V : AdelicVectorBundle (S.algebraicExtension L))
    (F : IntermediateField K L)
    [hD : (S.algebraicExtension L).NormMeasurabilityHypotheses]
    [hT : ((S.algebraicExtension F).algebraicExtension L).NormMeasurabilityHypotheses]
    [hND : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hNT : ((S.algebraicExtension F).algebraicExtension L).IsArchimedeanNormalized] :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
    (V.towerPullback F).degree = V.degree := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  change (V.towerPullback F).degree = V.degree
  let s := (V.determinantOfNormMeasurability).lineGenerator
    (hV := (V.determinantOfNormMeasurability_isLine))
  rw [degree_eq_neg_integral (V.towerPullback F) s, degree_eq_neg_integral V s]
  change -(∫ x, (V.toNormFamily.towerPullback F).determinant.logNorm s.val x
      ∂((S.algebraicExtension F).algebraicExtension L).v) =
    -(∫ x, V.toNormFamily.determinant.logNorm s.val x ∂(S.algebraicExtension L).v)
  rw [NormFamily.towerPullback_determinant, NormFamily.towerPullback_logNorm]
  exact congrArg (fun t : ℝ => -t)
    ((measurePreserving_scalarExtensionTowerPlace (S := S) F).integral_comp
      (AdelicStructure.Algebraic.towerMeasurableEquiv S F).measurableEmbedding _)

omit [FiniteDimensional L E] in
/-- A completed isometry over the tower compares degrees on the direct and iterated curves. -/
theorem degree_eq_of_tower_completed_isometry [S.IsProper]
    (F : IntermediateField K L)
    (W : AdelicVectorBundle ((S.algebraicExtension F).algebraicExtension L))
    (R : AdelicVectorBundle (S.algebraicExtension L)) (e : W ≃ₗ[L] R)
    [hD : (S.algebraicExtension L).NormMeasurabilityHypotheses]
    [hT : ((S.algebraicExtension F).algebraicExtension L).NormMeasurabilityHypotheses]
    [hND : (S.algebraicExtension L).IsArchimedeanNormalized]
    [hNT : ((S.algebraicExtension F).algebraicExtension L).IsArchimedeanNormalized]
    (he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (z : x.abv.Completion ⊗[L] W), R.toNormFamily.norm (scalarExtensionTowerPlace x)
        (e.toLinearMap.baseChange x.abv.Completion z) = W.toNormFamily.norm x z) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
    R.degree = W.degree := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  exact (R.degree_towerPullback F).symm.trans
    (W.degree_eq_of_completed_isometry (R.towerPullback F) e he).symm

end AdelicVectorBundle
end ArakelovGeometry

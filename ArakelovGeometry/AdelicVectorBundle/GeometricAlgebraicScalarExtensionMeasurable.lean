/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.GeometricScalarExtensionMeasurable
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDualDescent

/-!
# Actual algebraic scalar measurability on all-finite positive atomic bases

Actual finite-coordinate primal and dual norm factorizations reduce each rational
section to an actual finite extension. The accepted positive-atomic finite
regularity then descends along the measurable restricted-place map. The original
family need only be dominated: neither original measurability, ultrametricity,
countability nor discreteness of the original field or place space is assumed.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

private theorem allFinite_inf_empty (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) : S.Ωinf = ∅ := by
  ext ω
  exact ⟨fun h => False.elim (h (hS ω)), fun h => False.elim h⟩

private theorem allFinite_stage_normalization (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (F : AdelicStructure.FiniteIntermediateField K L) :
    ∀ x ∈ (S.algebraicExtension F).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension F).ϕ x).Completion := by
  intro x hx
  exact False.elim (hx ((scalarExtension_mem_Ωfin_iff x).mpr (hS x.base)))

private theorem measurable_actual_stage_restriction
    (F : AdelicStructure.FiniteIntermediateField K L) :
    @Measurable (S.algebraicExtension L).Ω (S.algebraicExtension F).Ω
      (S.algebraicExtension L).instMeasurableSpaceΩ
      (S.algebraicExtension F).instMeasurableSpaceΩ
      (fun x => AdelicStructure.ParameterSpaceExtension.restrict S L x F) := by
  change @Measurable _ _ (AdelicStructure.Algebraic.projectiveMeasurableSpace S L)
    (AdelicStructure.Algebraic.projectiveMeasurableSpace S F) _
  rw [AdelicStructure.Algebraic.projectiveMeasurableSpace_eq,
    AdelicStructure.Algebraic.projectiveMeasurableSpace_eq]
  exact AdelicStructure.ParameterSpaceExtension.measurable_restrict S L F.1

/-- Actual ordinary scalar measurability after every algebraic extension of
an all-finite positive atomic curve, from original domination alone. -/
theorem IsDominated.scalarExtension_isMeasurable_of_positive_atoms_of_isAlgebraic
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    (ξ.scalarExtension (L := L)).IsMeasurable := by
  have hfin : S.v S.Ωinf < ⊤ := by
    rw [allFinite_inf_empty hS, measure_empty]
    exact ENNReal.zero_lt_top
  intro z
  obtain ⟨F, y, hy⟩ := exists_finiteStage_tensor_lift z
  have hm := IsDominated.scalarExtension_isMeasurable_of_positive_atoms (L := F)
    ξ (Module.finBasis K E) hξ hpos hfin
  have he : (fun x : (S.algebraicExtension L).Ω =>
      (ξ.scalarExtension (L := L)).norm x
        ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] z)) =
      (fun x : (S.algebraicExtension L).Ω =>
        (ξ.scalarExtension (L := F)).norm
          (AdelicStructure.ParameterSpaceExtension.restrict S L x F)
          ((1 : (x.abv.restriction F).Completion) ⊗ₜ[F] y)) := by
    funext x
    rw [← hy]
    exact ξ.scalarExtension_norm_finiteStage F (allFinite_stage_normalization hS F) x y
  rw [he]
  exact (hm y).comp (measurable_actual_stage_restriction F)

/-- The genuine completed dual is measurable after arbitrary algebraic extension,
using actual functional finite-stage factorization rather than a regularity premise. -/
theorem IsDominated.scalarExtension_dual_isMeasurable_of_positive_atoms_of_isAlgebraic
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E) (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    (ξ.scalarExtension (L := L)).dual.IsMeasurable := by
  have hfin : S.v S.Ωinf < ⊤ := by
    rw [allFinite_inf_empty hS, measure_empty]
    exact ENNReal.zero_lt_top
  intro ℓ
  obtain ⟨F, y, hy⟩ := exists_finiteStage_tensor_lift
    ((dualBaseChangeEquiv K L E).symm ℓ)
  have hℓ : dualBaseChangeEquiv K L E
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L (Module.Dual K E)
        ((1 : L) ⊗ₜ[F] y)) = ℓ := by
    rw [hy, LinearEquiv.apply_symm_apply]
  have hm := IsDominated.scalarExtension_dual_isMeasurable_of_positive_atoms (L := F)
    ξ (Module.finBasis K E) hξ hpos hfin
  have he : (fun x : (S.algebraicExtension L).Ω =>
      (ξ.scalarExtension (L := L)).dual.norm x
        ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] ℓ)) =
      (fun x : (S.algebraicExtension L).Ω =>
        (ξ.scalarExtension (L := F)).dual.norm
          (AdelicStructure.ParameterSpaceExtension.restrict S L x F)
          ((1 : (x.abv.restriction F).Completion) ⊗ₜ[F] dualBaseChangeEquiv K F E y)) := by
    funext x
    rw [← hℓ]
    exact ξ.scalarExtension_dual_norm_finiteStage F x y
  rw [he]
  exact (hm (dualBaseChangeEquiv K F E y)).comp (measurable_actual_stage_restriction F)

/-- Over the actual projective-line curve, every dominated original family has
measurable ordinary scalar norms after every algebraic extension, for any constant field. -/
theorem IsDominated.functionField_algebraicScalarExtension_isMeasurable
    {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]
    [Algebra.IsAlgebraic (RatFunc k) L] {E : Type*} [AddCommGroup E]
    [Module (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) : (ξ.scalarExtension (L := L)).IsMeasurable := by
  apply IsDominated.scalarExtension_isMeasurable_of_positive_atoms_of_isAlgebraic
    ξ hξ AdelicStructure.functionField_singleton_pos
  intro ω
  by_contra h
  have hω : ω ∈ (AdelicStructure.functionFieldAdelicStructure k).Ωinf := h
  rw [AdelicStructure.functionField_Ωinf_eq_empty] at hω
  exact hω

/-- The actual completed dual of the ordinary algebraic extension is measurable
on the geometric projective-line curve, with no original regularity or countability premise. -/
theorem IsDominated.functionField_algebraicScalarExtension_dual_isMeasurable
    {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]
    [Algebra.IsAlgebraic (RatFunc k) L] {E : Type*} [AddCommGroup E]
    [Module (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) : (ξ.scalarExtension (L := L)).dual.IsMeasurable := by
  apply IsDominated.scalarExtension_dual_isMeasurable_of_positive_atoms_of_isAlgebraic
    ξ hξ AdelicStructure.functionField_singleton_pos
  intro ω
  by_contra h
  have hω : ω ∈ (AdelicStructure.functionFieldAdelicStructure k).Ωinf := h
  rw [AdelicStructure.functionField_Ωinf_eq_empty] at hω
  exact hω

end ArakelovGeometry.NormFamily

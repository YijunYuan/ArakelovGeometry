/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianScalarExtensionMeasurable
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscrete

/-!
# Hermitian scalar extension over a countable discrete base

Actual finite-stage descent proves the corrected discrete alternative of
Chen–Moriwaki Proposition 4.1.24(1.c), without a common dense subfield.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wE

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  {S : AdelicStructure.{u, v} K}
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Algebra.IsAlgebraic K L] (ξ : NormFamily S E)
  (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hH : ξ.IsHermitian hS)

/-- Finite Hermitian scalar extension is measurable on the actual discrete
extending parameter space; normalization is produced from the original base. -/
theorem hermitianScalarExtension_isMeasurable_of_finiteDimensional_of_countable_discrete
    [FiniteDimensional K L] [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    (hermitianScalarExtension ξ hS
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hS) hH).IsMeasurable := by
  let := AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
    (S := S) (L := L)
  exact isMeasurable_of_discrete (hermitianScalarExtension ξ hS
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hS) hH)

/-- Corrected source4.1.24(1.c): actual Hermitian scalar extension is measurable
for every algebraic extension of a countable discrete base, in every rank.
No common dense subfield or measurability premise on the target is assumed. -/
theorem hermitianScalarExtension_isMeasurable_of_countable_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    (hermitianScalarExtension ξ hS
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hS) hH).IsMeasurable := by
  intro z
  obtain ⟨F, y, hy⟩ := exists_finiteStage_tensor_lift z
  let hF := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hS
  let hL := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hS
  have hm := hermitianScalarExtension_isMeasurable_of_finiteDimensional_of_countable_discrete
    (L := F) ξ hS hH
  have hr : @Measurable (S.algebraicExtension L).Ω (S.algebraicExtension F).Ω
      (S.algebraicExtension L).instMeasurableSpaceΩ
      (S.algebraicExtension F).instMeasurableSpaceΩ
      (fun x => AdelicStructure.ParameterSpaceExtension.restrict S L x F) := by
    change @Measurable _ _ (AdelicStructure.Algebraic.projectiveMeasurableSpace S L)
      (AdelicStructure.Algebraic.projectiveMeasurableSpace S F) _
    rw [AdelicStructure.Algebraic.projectiveMeasurableSpace_eq,
      AdelicStructure.Algebraic.projectiveMeasurableSpace_eq]
    exact AdelicStructure.ParameterSpaceExtension.measurable_restrict S L F.1
  have he : (fun x : (S.algebraicExtension L).Ω =>
      (hermitianScalarExtension ξ hS hL hH).norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] z)) =
      (fun x : (S.algebraicExtension L).Ω =>
        (hermitianScalarExtension ξ hS hF hH).norm
          (AdelicStructure.ParameterSpaceExtension.restrict S L x F)
          ((1 : (x.abv.under F).Completion) ⊗ₜ[F] y)) := by
    funext x
    rw [← hy]
    exact hermitianScalarExtension_norm_finiteStage ξ hS hL hH F hF x y
  exact he.symm ▸ (hm y).comp hr

end ArakelovGeometry.NormFamily

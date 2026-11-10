/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionQuotientEquiv
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDegreeDeterminant
import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminantIsometry

/-!
# Actual native subspace and quotient degrees over a countable discrete base

Finite-stage determinant measurability, canonical completed norm isometries
and actual measure-preserving place towers produce the target determinant
measurability and degree, without target discreteness or common density.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

namespace NormFamily

private theorem discreteNative_measurable_of_towerPullback
    {X : Type*} [AddCommGroup X] [Module L X]
    (ξ : NormFamily (S.algebraicExtension L) X) (F : IntermediateField K L)
    (hξ : (ξ.towerPullback F).IsMeasurable) : ξ.IsMeasurable := by
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

variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- Finite-stage determinant measurability and an actual completed restriction
isometry produce measurability of every prescribed native target determinant. -/
theorem scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
    (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    ((ξ.scalarExtension (L := L)).restrict A).determinant.IsMeasurable := by
  obtain ⟨F, _, B, _, _, he⟩ := ξ.exists_complexFiniteStage_restriction_isometries hN
    (fun _ : Fin 1 => A)
  obtain ⟨e, he⟩ := he 0
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  let η₀ := (ξ.scalarExtension (L := F)).restrict (B 0)
  let η := η₀.scalarExtension (L := L)
  let θ := (ξ.scalarExtension (L := L)).restrict A
  have hm : η.determinant.IsMeasurable :=
    (η₀.isMeasurable_of_discrete.determinant_of_discrete_or_countable
      (Or.inl inferInstance)).determinant_scalarExtension
  have ht : (θ.towerPullback F.toIntermediateField).determinant.IsMeasurable :=
    η.determinant_isMeasurable_of_completed_isometry
      (θ.towerPullback F.toIntermediateField) e he hm
  rw [towerPullback_determinant] at ht
  exact discreteNative_measurable_of_towerPullback θ.determinant F.toIntermediateField ht

/-- The canonical actual quotient isometry produces determinant measurability
for every native target quotient, without any extended place-space regularity. -/
theorem scalarExtension_quotient_determinant_isMeasurable_of_countable_discrete
    (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    ((ξ.scalarExtension (L := L)).quotient A).determinant.IsMeasurable := by
  obtain ⟨F, hi, B, hB, _, _⟩ := exists_complexFiniteStage_subspaces
    (fun _ : Fin 1 => A)
  have ha := hB 0
  subst A
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let e := finiteStageQuotientEquiv F (B 0)
  let η₀ := (ξ.scalarExtension (L := F)).quotient (B 0)
  let η := η₀.scalarExtension (L := L)
  let θ := (ξ.scalarExtension (L := L)).quotient (((B 0).baseChange L).map c.toLinearMap)
  have hm : η.determinant.IsMeasurable :=
    (η₀.isMeasurable_of_discrete.determinant_of_discrete_or_countable
      (Or.inl inferInstance)).determinant_scalarExtension
  have ht : (θ.towerPullback F.toIntermediateField).determinant.IsMeasurable :=
    η.determinant_isMeasurable_of_completed_isometry
      (θ.towerPullback F.toIntermediateField) e
      (fun x z => ξ.scalarExtension_quotient_finiteStage_equiv_norm_eq hN F hi (B 0) x z) hm
  rw [towerPullback_determinant] at ht
  exact discreteNative_measurable_of_towerPullback θ.determinant F.toIntermediateField ht

end NormFamily
end ArakelovGeometry

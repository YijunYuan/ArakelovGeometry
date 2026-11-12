/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.FiniteStage.RestrictionIsometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.QuotientEquiv
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.ComplexDescent
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.DeterminantDegree
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual native subspace and quotient degrees over a countable discrete base

Finite-stage determinant measurability, canonical completed norm isometries
and actual measure-preserving place towers produce the target determinant
measurability and degree, without target discreteness or common density.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

namespace NormFamily

variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- Finite-stage determinant measurability and an actual completed restriction
isometry produce measurability of every prescribed native target determinant. -/
theorem scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
    (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule L (L ⊗[K] E)) :
    ((ξ.scalarExtension (L := L)).restrict A).determinant.IsMeasurable := by
  obtain ⟨F, _, B, _, _, he⟩ := ξ.exists_complexFiniteStage_restriction_isometries
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
     ).determinant_scalarExtension
  exact determinant_isMeasurable_of_tower_completed_isometry F.toIntermediateField η θ e he
      (hm := hm)

/-- The canonical actual quotient isometry produces determinant measurability
for every native target quotient, without any extended place-space regularity. -/
theorem scalarExtension_quotient_determinant_isMeasurable_of_countable_discrete
    (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
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
  let e := finiteStageQuotientEquiv (L := L) F (B 0)
  let η₀ := (ξ.scalarExtension (L := F)).quotient (B 0)
  let η := η₀.scalarExtension (L := L)
  let θ := (ξ.scalarExtension (L := L)).quotient (((B 0).baseChange L).map c.toLinearMap)
  have hm : η.determinant.IsMeasurable :=
    (η₀.isMeasurable_of_discrete.determinant_of_discrete_or_countable
     ).determinant_scalarExtension
  exact determinant_isMeasurable_of_tower_completed_isometry F.toIntermediateField η θ e
    (fun x z ↦ ξ.scalarExtension_quotient_finiteStage_equiv_norm_eq F hi (B 0) x z) (hm := hm)

end NormFamily
end ArakelovGeometry

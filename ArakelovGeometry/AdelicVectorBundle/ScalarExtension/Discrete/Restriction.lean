/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Bundle

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Dual.Descent
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.FiniteStage.RestrictionIsometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Transport
import Mathlib.CategoryTheory.Category.Init

/-!
# Native restrictions over the algebraic closure of a countable discrete base

A produced complexifying finite field of definition supplies an actual native
finite-stage restriction. Its further scalar extension has measurable dual
norms. Actual completed tensor isometries and dual pairing transport identify
these with the native target restriction dual norms under the measurable tower
place equivalence. No discreteness or common density is assumed on the target.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v w wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

namespace NormFamily

variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- Every native restricted dual of the actual ordinary scalar family is
measurable over the algebraic closure, without any target base hypothesis. -/
theorem scalarExtension_restrict_dual_isMeasurable_of_countable_discrete
    (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule L (L ⊗[K] E)) :
    ((ξ.scalarExtension (L := L)).restrict A).dual.IsMeasurable := by
  obtain ⟨F, _, B, _, _, he⟩ := ξ.exists_complexFiniteStage_restriction_isometries
    (fun _ : Fin 1 => A)
  obtain ⟨e, he⟩ := he 0
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  let η := ((ξ.scalarExtension (L := F)).restrict (B 0)).scalarExtension (L := L)
  let θ := (ξ.scalarExtension (L := L)).restrict A
  have hm : η.dual.IsMeasurable :=
    NormFamily.scalarExtension_dual_isMeasurable_of_countable_discrete
      ((ξ.scalarExtension (L := F)).restrict (B 0))
  exact IsMeasurable.dual_of_tower_completed_isometry F η θ e he hm

end NormFamily

namespace AdelicVectorBundle
variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- The genuine native target restriction bundle, constructed from its actual
primal and produced dual measurability; target discreteness is unnecessary. -/
abbrev scalarExtensionRestrictionOfCountableDiscreteBase
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule L (L ⊗[K] V)) : AdelicVectorBundle (S.algebraicExtension L) :=
  (V.scalarExtensionOfCountableDiscreteBase (L := L)).restrict A
    (hm := (V.toNormFamily.scalarExtension_restrict_dual_isMeasurable_of_countable_discrete A))

@[simp]
theorem scalarExtensionRestrictionOfCountableDiscreteBase_toNormFamily
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule L (L ⊗[K] V)) :
    (V.scalarExtensionRestrictionOfCountableDiscreteBase (L := L) A).toNormFamily =
      (V.toNormFamily.scalarExtension (L := L)).restrict A := rfl

end AdelicVectorBundle
end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteSubquotient

/-!
# Native restrictions over the algebraic closure of a countable discrete base

A produced complexifying finite field of definition supplies an actual native
finite-stage restriction. Its further scalar extension has measurable dual
norms. Actual completed tensor isometries and dual pairing transport identify
these with the native target restriction dual norms under the measurable tower
place equivalence. No discreteness or common density is assumed on the target.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v w wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

namespace NormFamily

/-- Actual completed isometry transports dual norms across the canonical
place tower. The proof uses the genuine completed dual pairing and every vector. -/
private theorem discreteRestriction_dual_norm_eq
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

variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- Every native restricted dual of the actual ordinary scalar family is
measurable over the algebraic closure, without any target base hypothesis. -/
theorem scalarExtension_restrict_dual_isMeasurable_of_countable_discrete
    (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    ((ξ.scalarExtension (L := L)).restrict A).dual.IsMeasurable := by
  obtain ⟨F, _, B, _, _, he⟩ := ξ.exists_complexFiniteStage_restriction_isometries hN
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
  intro ℓ
  let τ := (AdelicStructure.Algebraic.towerMeasurableEquiv S F.toIntermediateField).symm
  have hnorm : (fun x : (S.algebraicExtension L).Ω =>
      θ.dual.norm x ((1 : x.abv.Completion) ⊗ₜ[L] ℓ)) =
      (fun x : (S.algebraicExtension L).Ω =>
        η.dual.norm (τ x) ((1 : (τ x).abv.Completion) ⊗ₜ[L] e.dualMap ℓ)) := by
    funext x
    have h := discreteRestriction_dual_norm_eq F η θ e (τ x) (he (τ x))
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

end NormFamily

namespace AdelicVectorBundle
variable {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- The genuine native target restriction bundle, constructed from its actual
primal and produced dual measurability; target discreteness is unnecessary. -/
def scalarExtensionRestrictionOfCountableDiscreteBase
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) : AdelicVectorBundle (S.algebraicExtension L) A :=
  (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).restrict A
    (V.toNormFamily.scalarExtension_restrict_dual_isMeasurable_of_countable_discrete hN A)

@[simp]
theorem scalarExtensionRestrictionOfCountableDiscreteBase_toNormFamily
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    (V.scalarExtensionRestrictionOfCountableDiscreteBase (L := L) hN A).toNormFamily =
      (V.toNormFamily.scalarExtension (L := L)).restrict A := rfl

end AdelicVectorBundle
end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionQuotientEquiv

/-!
# Genuine native subquotients over an algebraic closure

For a countable discrete original place space, every quotient of an actual
native restricted scalar-extension family has produced primal measurability.
Finite descent of the restricted space and completed quotient transport supply
this property without any regularity assumption on the target place space.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v w wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

namespace NormFamily

omit [IsAlgClosed L] [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] in
private theorem discreteSubquotient_quotient_norm_eq
    (F : AdelicStructure.FiniteIntermediateField K L)
    {X Y : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension L) X)
    (θ : NormFamily (S.algebraicExtension L) Y) (e : X ≃ₗ[L] Y)
    (P : Submodule L X)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (he : ∀ t, θ.norm (scalarExtensionTowerPlace x)
      (e.toLinearMap.baseChange x.abv.Completion t) = η.norm x t)
    (z : x.abv.Completion ⊗[L] (X ⧸ P)) :
    let Q := P.map e.toLinearMap
    let q := Submodule.Quotient.equiv P Q e rfl
    (θ.quotient Q).norm (scalarExtensionTowerPlace x)
      (q.toLinearMap.baseChange x.abv.Completion z) = (η.quotient P).norm x z := by
  intro Q q
  have h := quotientEquiv_norm_eq (k := L)
    (T := (S.algebraicExtension F).algebraicExtension L)
    η (θ.towerPullback F.toIntermediateField) x e P he z
  dsimp only at h
  rw [towerPullback_quotient] at h
  exact h

omit [IsAlgClosed L] [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] in
private theorem discreteSubquotient_isMeasurable
    (F : AdelicStructure.FiniteIntermediateField K L)
    {X Y : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension L) X)
    (θ : NormFamily (S.algebraicExtension L) Y) (e : X ≃ₗ[L] Y)
    (P : Submodule L X)
    (he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (t : x.abv.Completion ⊗[L] X), θ.norm (scalarExtensionTowerPlace x)
        (e.toLinearMap.baseChange x.abv.Completion t) = η.norm x t)
    (hm : (η.quotient P).IsMeasurable) :
    (θ.quotient (P.map e.toLinearMap)).IsMeasurable := by
  let Q := P.map e.toLinearMap
  let q := Submodule.Quotient.equiv P Q e rfl
  intro y
  let τ := (AdelicStructure.Algebraic.towerMeasurableEquiv S F.toIntermediateField).symm
  have hnorm : (fun x : (S.algebraicExtension L).Ω =>
      (θ.quotient Q).norm x ((1 : x.abv.Completion) ⊗ₜ[L] y)) =
      (fun x : (S.algebraicExtension L).Ω =>
        (η.quotient P).norm (τ x)
          ((1 : (τ x).abv.Completion) ⊗ₜ[L] q.symm y)) := by
    funext x
    have h := discreteSubquotient_quotient_norm_eq F η θ e P (τ x) (he (τ x))
      ((1 : (τ x).abv.Completion) ⊗ₜ[L] q.symm y)
    dsimp only at h
    have hv : q.toLinearMap.baseChange (τ x).abv.Completion
        ((1 : (τ x).abv.Completion) ⊗ₜ[L] q.symm y) =
        (1 : (τ x).abv.Completion) ⊗ₜ[L] y := by
      simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, q.apply_symm_apply]
    have hn := congrArg
      (fun z : (τ x).abv.Completion ⊗[L] (Y ⧸ Q) => (θ.quotient Q).norm x z) hv
    exact hn.symm.trans h
  change Measurable (fun x : (S.algebraicExtension L).Ω =>
    (θ.quotient Q).norm x ((1 : x.abv.Completion) ⊗ₜ[L] y))
  rw [hnorm]
  exact (hm (q.symm y)).comp τ.measurable

/-- Every actual quotient of a native restricted scalar family has produced
primal measurability. The target places need not be discrete or have a common
dense subfield; neither source measurability nor original ultrametricity is
assumed for the norm family. -/
theorem scalarExtension_restrict_quotient_isMeasurable_of_countable_discrete
    (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) (T : Submodule L A) :
    (((ξ.scalarExtension (L := L)).restrict A).quotient T).IsMeasurable := by
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
  let P := T.comap e.toLinearMap
  let Q := P.map e.toLinearMap
  have hQ : Q = T := Submodule.map_comap_eq_of_surjective e.surjective T
  have hm : (η.quotient P).IsMeasurable :=
    scalarExtension_quotient_isMeasurable_of_countable_discrete
      ((ξ.scalarExtension (L := F)).restrict (B 0))
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN) P
  change (θ.quotient T).IsMeasurable
  rw [← hQ]
  exact discreteSubquotient_isMeasurable F η θ e P he hm

end NormFamily
namespace AdelicVectorBundle

/-- The actual quotient of a native restricted scalar bundle over an algebraic
closure, with primal measurability produced from a countable discrete base. -/
def scalarExtensionSubspaceQuotientOfCountableDiscreteBase
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) (T : Submodule L A) :
    AdelicVectorBundle (S.algebraicExtension L) (A ⧸ T) :=
  (V.scalarExtensionRestrictionOfCountableDiscreteBase (L := L) hN A).quotient T
    (V.toNormFamily.scalarExtension_restrict_quotient_isMeasurable_of_countable_discrete hN A T)

@[simp]
theorem scalarExtensionSubspaceQuotientOfCountableDiscreteBase_toNormFamily
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) (T : Submodule L A) :
    (V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase (L := L) hN A T).toNormFamily =
      ((V.toNormFamily.scalarExtension (L := L)).restrict A).quotient T := rfl

end AdelicVectorBundle
end ArakelovGeometry

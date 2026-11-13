/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Subquotient
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Bundle
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Transport

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.ComplexQuotient
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.ComplexDescent
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Basic
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.CategoryTheory.Category.Init

/-!
# Genuine native quotient norms over algebraic closures

Canonical tensor quotient equivalences and tower cancellation transport all
completed lift sets. Complexifying finite descent then supplies primal
measurability for the prescribed native target quotients over countable
discrete original place spaces, without target discreteness or common density.

Transport is first proved for arbitrary norm families and commuting quotient maps.
Specializing only after composing these identities keeps the tower proofs independent
of the concrete scalar-extension norm construction.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u w wE
variable {K : Type u} [Field K] {S : AdelicStructure K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

section TensorQuotient
variable {k : Type*} [Field k] {l : Type*} [Field l] [Algebra k l]
  {X : Type*} [AddCommGroup X] [Module k X]

/-- Tensoring a submodule inclusion has the base-changed submodule as its range. -/
theorem discreteTensorQuotient_range_eq (P : Submodule k X) :
    (TensorProduct.AlgebraTensorModule.lTensor (R := k) l l
      (P.subtype.restrictScalars k)).range = P.baseChange l := by
  congr 1

/-- Scalar extension commutes with taking a quotient by a submodule. -/
def discreteTensorQuotientEquiv (P : Submodule k X) :
    (l ⊗[k] (X ⧸ P)) ≃ₗ[l] ((l ⊗[k] X) ⧸ P.baseChange l) :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := k) l k l P).trans
    (Submodule.quotEquivOfEq _ _ (discreteTensorQuotient_range_eq P))

private theorem discreteTensorQuotientEquiv_comp_mkQ (P : Submodule k X) :
    (discreteTensorQuotientEquiv (l := l) P).toLinearMap.comp (P.mkQ.baseChange l) =
      (P.baseChange l).mkQ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a y
  rfl

variable [Algebra.IsAlgebraic k l] {T : AdelicStructure k} [FiniteDimensional k X]

private theorem tensorQuotient_norm_eq_of_comp_eq (ξ : NormFamily T X)
    [hN : T.IsArchimedeanNormalized]
    (hi : ∃ a : k, a ^ 2 = -1) (P : Submodule k X)
    (e : (l ⊗[k] (X ⧸ P)) ≃ₗ[l] ((l ⊗[k] X) ⧸ P.baseChange l))
    (he : e.toLinearMap.comp (P.mkQ.baseChange l) = (P.baseChange l).mkQ)
    (x : T.ParameterSpaceExtension l) (z : x.abv.Completion ⊗[l] (l ⊗[k] (X ⧸ P))) :
    ((ξ.scalarExtension (L := l)).quotient (P.baseChange l)).norm x
        (e.toLinearMap.baseChange x.abv.Completion z) =
      ((ξ.quotient P).scalarExtension (L := l)).norm x z := by
  let η := ξ.scalarExtension (L := l)
  let ω : (T.algebraicExtension l).Ω := x
  change ((T.algebraicExtension l).ϕ ω).Completion ⊗[l] (l ⊗[k] (X ⧸ P)) at z
  have hc := η.pushforward_comp_norm (P.mkQ.baseChange l)
    (LinearMap.baseChange_surjective l P.mkQ_surjective) e.toLinearMap e.surjective ω
      (e.toLinearMap.baseChange ((T.algebraicExtension l).ϕ ω).Completion z)
  simp only [he] at hc
  have ht := (η.pushforward (P.mkQ.baseChange l)
    (LinearMap.baseChange_surjective l P.mkQ_surjective)).pushforward_norm_of_injective
    e.toLinearMap e.surjective e.injective ω z
  exact (hc.symm.trans ht).trans
    (ξ.scalarExtension_pushforward_norm_eq_of_sqrt_neg_one hi P.mkQ P.mkQ_surjective x z)

end TensorQuotient

/-- The canonical place tower transport commutes with genuine quotient
norms on the identical completed fibre. -/
theorem towerPullback_quotient {X : Type*} [AddCommGroup X] [Module L X]
    [FiniteDimensional L X] (ξ : NormFamily (S.algebraicExtension L) X)
    (F : IntermediateField K L) (A : Submodule L X) :
    (ξ.towerPullback F).quotient A = (ξ.quotient A).towerPullback F := by
  ext x z
  rfl

private theorem quotientEquiv_towerPullback_norm_eq
    {F : Type*} [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L]
    {X Y : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension L) X)
    (θ : NormFamily (S.algebraicExtension L) Y)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (e : X ≃ₗ[L] Y) (P : Submodule L X) (A : Submodule L Y)
    (q : (X ⧸ P) ≃ₗ[L] (Y ⧸ A))
    (hc : q.toLinearMap.comp P.mkQ = A.mkQ.comp e.toLinearMap)
    (he : ∀ t, θ.norm (scalarExtensionTowerPlace x)
      (e.toLinearMap.baseChange x.abv.Completion t) = η.norm x t)
    (z : x.abv.Completion ⊗[L] (X ⧸ P)) :
    (θ.quotient A).norm (scalarExtensionTowerPlace x)
      (q.toLinearMap.baseChange x.abv.Completion z) = (η.quotient P).norm x z := by
  let θ' : NormFamily ((S.algebraicExtension F).algebraicExtension L) Y :=
    { norm x := θ.norm (scalarExtensionTowerPlace x)
      norm_eq_zero_iff x := θ.norm_eq_zero_iff (scalarExtensionTowerPlace x) }
  exact quotientEquiv_norm_eq_of_comp_eq η θ' x e P A q hc he z

private theorem scalarExtension_quotient_tower_norm_eq
    {F : Type*} [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L]
    {X Y : Type*} [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (η : NormFamily (S.algebraicExtension F) X)
    (θ : NormFamily (S.algebraicExtension L) Y)
    [hN : (S.algebraicExtension F).IsArchimedeanNormalized]
    (hi : ∃ a : F, a ^ 2 = -1)
    (c : (L ⊗[F] X) ≃ₗ[L] Y) (B : Submodule F X) (A : Submodule L Y)
    (q : ((L ⊗[F] X) ⧸ B.baseChange L) ≃ₗ[L] (Y ⧸ A))
    (hq : q.toLinearMap.comp (B.baseChange L).mkQ = A.mkQ.comp c.toLinearMap)
    (d : (L ⊗[F] (X ⧸ B)) ≃ₗ[L] ((L ⊗[F] X) ⧸ B.baseChange L))
    (hd : d.toLinearMap.comp (B.mkQ.baseChange L) = (B.baseChange L).mkQ)
    (hc : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (t : x.abv.Completion ⊗[L] (L ⊗[F] X)),
      θ.norm (scalarExtensionTowerPlace x) (c.toLinearMap.baseChange x.abv.Completion t) =
        (η.scalarExtension (L := L)).norm x t)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (z : x.abv.Completion ⊗[L] (L ⊗[F] (X ⧸ B))) :
    (θ.quotient A).norm (scalarExtensionTowerPlace x)
      (q.toLinearMap.baseChange x.abv.Completion
        (d.toLinearMap.baseChange x.abv.Completion z)) =
      ((η.quotient B).scalarExtension (L := L)).norm x z := by
  exact (quotientEquiv_towerPullback_norm_eq (η.scalarExtension (L := L)) θ x c
    (B.baseChange L) A q hq (hc x) (d.toLinearMap.baseChange x.abv.Completion z)).trans
      (tensorQuotient_norm_eq_of_comp_eq η hi B d hd x z)

/-- Quotient norms commute with scalar extension through a complexifying algebraic tower.
In particular, this identifies the native target quotient with any finite-stage quotient. -/
theorem scalarExtension_quotient_finiteStage_norm_eq (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L]
    (hi : ∃ a : F, a ^ 2 = -1)
    (B : Submodule F (F ⊗[K] E))
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (z : x.abv.Completion ⊗[L] (L ⊗[F] ((F ⊗[K] E) ⧸ B))) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (B.baseChange L).map c.toLinearMap
    let d := discreteTensorQuotientEquiv (l := L) B
    let q := Submodule.Quotient.equiv (B.baseChange L) A c rfl
    ((ξ.scalarExtension (L := L)).quotient A).norm (scalarExtensionTowerPlace x)
      (q.toLinearMap.baseChange x.abv.Completion
        (d.toLinearMap.baseChange x.abv.Completion z)) =
      (((ξ.scalarExtension (L := F)).quotient B).scalarExtension (L := L)).norm x z := by
  intro c A d q
  exact scalarExtension_quotient_tower_norm_eq
    (K := K) (S := S) (L := L) (F := F)
    (X := F ⊗[K] E) (Y := L ⊗[K] E)
    (ξ.scalarExtension (L := F)) (ξ.scalarExtension (L := L))
    hi c B A q (by ext y; rfl) d (discreteTensorQuotientEquiv_comp_mkQ B)
    (fun x t ↦ (ξ.scalarExtension_trans x t).symm) x z

private theorem isMeasurable_of_quotient_tower_norm_eq
    (F : AdelicStructure.FiniteIntermediateField K L)
    {X Y Z : Type*} [AddCommGroup X] [Module L X]
    [AddCommGroup Y] [Module L Y] [AddCommGroup Z] [Module L Z]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension L) X)
    (θ : NormFamily (S.algebraicExtension L) Z) (d : X ≃ₗ[L] Y) (q : Y ≃ₗ[L] Z)
    (he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (z : x.abv.Completion ⊗[L] X),
      θ.norm (scalarExtensionTowerPlace x) (q.toLinearMap.baseChange x.abv.Completion
        (d.toLinearMap.baseChange x.abv.Completion z)) = η.norm x z)
    (hm : η.IsMeasurable) : θ.IsMeasurable := by
  constructor
  intro y
  apply (AdelicStructure.Algebraic.towerMeasurableEquiv S
    F.toIntermediateField).measurable_comp_iff.mp
  have hnorm : (fun x : ((S.algebraicExtension F).algebraicExtension L).Ω =>
      θ.norm (scalarExtensionTowerPlace x) ((1 : x.abv.Completion) ⊗ₜ[L] y)) =
      (fun x : ((S.algebraicExtension F).algebraicExtension L).Ω =>
        η.norm x ((1 : x.abv.Completion) ⊗ₜ[L] d.symm (q.symm y))) := by
    funext x
    have hd : d.toLinearMap.baseChange x.abv.Completion
        ((1 : x.abv.Completion) ⊗ₜ[L] d.symm (q.symm y)) =
        (1 : x.abv.Completion) ⊗ₜ[L] q.symm y := by
      simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, d.apply_symm_apply]
    have hq : q.toLinearMap.baseChange x.abv.Completion
        ((1 : x.abv.Completion) ⊗ₜ[L] q.symm y) =
        (1 : x.abv.Completion) ⊗ₜ[L] y := by
      simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, q.apply_symm_apply]
    have hv := congrArg (q.toLinearMap.baseChange x.abv.Completion) hd
    have hn := congrArg (fun z : x.abv.Completion ⊗[L] Z =>
      θ.norm (scalarExtensionTowerPlace x) z) (hv.trans hq)
    exact hn.symm.trans (he x ((1 : x.abv.Completion) ⊗ₜ[L] d.symm (q.symm y)))
  change Measurable (fun x : ((S.algebraicExtension F).algebraicExtension L).Ω =>
    θ.norm (scalarExtensionTowerPlace x) ((1 : x.abv.Completion) ⊗ₜ[L] y))
  rw [hnorm]
  exact hm (d.symm (q.symm y))

private theorem scalarExtension_quotient_isMeasurable_of_tower
    (F : AdelicStructure.FiniteIntermediateField K L)
    {X Y : Type*} [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (η : NormFamily (S.algebraicExtension F) X)
    (θ : NormFamily (S.algebraicExtension L) Y)
    [hN : (S.algebraicExtension F).IsArchimedeanNormalized]
    (hi : ∃ a : F, a ^ 2 = -1)
    (c : (L ⊗[F] X) ≃ₗ[L] Y) (B : Submodule F X) (A : Submodule L Y)
    (q : ((L ⊗[F] X) ⧸ B.baseChange L) ≃ₗ[L] (Y ⧸ A))
    (hq : q.toLinearMap.comp (B.baseChange L).mkQ = A.mkQ.comp c.toLinearMap)
    (d : (L ⊗[F] (X ⧸ B)) ≃ₗ[L] ((L ⊗[F] X) ⧸ B.baseChange L))
    (hd : d.toLinearMap.comp (B.mkQ.baseChange L) = (B.baseChange L).mkQ)
    (hc : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (t : x.abv.Completion ⊗[L] (L ⊗[F] X)),
      θ.norm (scalarExtensionTowerPlace x) (c.toLinearMap.baseChange x.abv.Completion t) =
        (η.scalarExtension (L := L)).norm x t)
    (hm : ((η.quotient B).scalarExtension (L := L)).IsMeasurable) :
    (θ.quotient A).IsMeasurable := by
  exact isMeasurable_of_quotient_tower_norm_eq F
    ((η.quotient B).scalarExtension (L := L)) (θ.quotient A) d q
    (scalarExtension_quotient_tower_norm_eq η θ hi c B A q hq d hd hc) hm

variable [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- Every actual native target quotient has produced primal measurability
over a countable discrete original base. No target regularity is assumed. -/
theorem scalarExtension_quotient_isMeasurable_of_countable_discrete (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule L (L ⊗[K] E)) :
    ((ξ.scalarExtension (L := L)).quotient A).IsMeasurable := by
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
  let A := ((B 0).baseChange L).map c.toLinearMap
  let q := Submodule.Quotient.equiv ((B 0).baseChange L) A c rfl
  let d := discreteTensorQuotientEquiv (l := L) (B 0)
  let η := ((ξ.scalarExtension (L := F)).quotient (B 0)).scalarExtension (L := L)
  have hm : η.IsMeasurable :=
    ((ξ.scalarExtension (L := F)).quotient (B 0)).scalarExtension_isMeasurable_of_countable_discrete
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩)
  exact scalarExtension_quotient_isMeasurable_of_tower F
    (ξ.scalarExtension (L := F)) (ξ.scalarExtension (L := L))
    hi
    c (B 0) A q (by ext y; rfl) d (discreteTensorQuotientEquiv_comp_mkQ (B 0))
    (fun x t ↦ (ξ.scalarExtension_trans x t).symm) hm

end NormFamily

namespace AdelicVectorBundle
variable [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- The genuine native target quotient bundle, with primal measurability
produced from finite descent and completed norm transport. -/
abbrev scalarExtensionQuotientOfCountableDiscreteBase (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule L (L ⊗[K] V)) :
    AdelicVectorBundle (S.algebraicExtension L) :=
  (V.scalarExtensionOfCountableDiscreteBase (L := L)).quotient A
    (hm := (V.toNormFamily.scalarExtension_quotient_isMeasurable_of_countable_discrete A))

@[simp]
theorem scalarExtensionQuotientOfCountableDiscreteBase_toNormFamily
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (A : Submodule L (L ⊗[K] V)) :
    (V.scalarExtensionQuotientOfCountableDiscreteBase (L := L) A).toNormFamily =
      (V.toNormFamily.scalarExtension (L := L)).quotient A := rfl

end AdelicVectorBundle
end ArakelovGeometry

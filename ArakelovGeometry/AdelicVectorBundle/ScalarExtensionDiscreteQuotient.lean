/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteRestriction
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionComplexQuotient
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTowerTransport

/-!
# Genuine native quotient norms over algebraic closures

Canonical tensor quotient equivalences and tower cancellation transport all
completed lift sets. Complexifying finite descent then supplies primal
measurability for the prescribed native target quotients over countable
discrete original place spaces, without target discreteness or common density.
-/

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v w wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

section Isometry
variable {k : Type*} [Field k] {T : AdelicStructure k}
  {X Y : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
  [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]

/-- An actual completed isometry induces the canonical quotient-image
isometry. Every completed lift is used; an optimal lift is unnecessary. -/
theorem quotientEquiv_norm_eq (ξ : NormFamily T X) (η : NormFamily T Y)
    (ω : T.Ω) (e : X ≃ₗ[k] Y) (P : Submodule k X)
    (he : ∀ t, η.norm ω (e.toLinearMap.baseChange (T.ϕ ω).Completion t) = ξ.norm ω t)
    (z : (T.ϕ ω).Completion ⊗[k] (X ⧸ P)) :
    let Q := P.map e.toLinearMap
    let q := Submodule.Quotient.equiv P Q e rfl
    (η.quotient Q).norm ω (q.toLinearMap.baseChange (T.ϕ ω).Completion z) =
      (ξ.quotient P).norm ω z := by
  intro Q q
  have hc : q.toLinearMap.comp P.mkQ = Q.mkQ.comp e.toLinearMap := by
    ext y
    rfl
  have hcb : (q.toLinearMap.baseChange (T.ϕ ω).Completion).comp
      (P.mkQ.baseChange (T.ϕ ω).Completion) =
      (Q.mkQ.baseChange (T.ϕ ω).Completion).comp
        (e.toLinearMap.baseChange (T.ϕ ω).Completion) := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hc]
  apply le_antisymm
  · apply (ξ.le_quotientSeminorm_iff P.mkQ P.mkQ_surjective ω z _).2
    intro t ht
    have hl : Q.mkQ.baseChange (T.ϕ ω).Completion
        (e.toLinearMap.baseChange (T.ϕ ω).Completion t) =
        q.toLinearMap.baseChange (T.ϕ ω).Completion z := by
      have h := congrArg (fun f : _ →ₗ[(T.ϕ ω).Completion] _ => f t) hcb
      simpa only [LinearMap.comp_apply, ht] using h.symm
    rw [← hl]
    exact (η.pushforward_norm_le Q.mkQ Q.mkQ_surjective ω _).trans (he t).le
  · apply (η.le_quotientSeminorm_iff Q.mkQ Q.mkQ_surjective ω _ _).2
    intro y hy
    obtain ⟨t, rfl⟩ := LinearMap.baseChange_surjective (T.ϕ ω).Completion e.surjective y
    have hl : P.mkQ.baseChange (T.ϕ ω).Completion t = z := by
      apply Module.Flat.lTensor_preserves_injective_linearMap q.toLinearMap q.injective
      have h := congrArg (fun f : _ →ₗ[(T.ϕ ω).Completion] _ => f t) hcb
      exact h.trans hy
    rw [← hl]
    exact (ξ.pushforward_norm_le P.mkQ P.mkQ_surjective ω t).trans (he t).symm.le

end Isometry

section TensorQuotient
variable {k : Type*} [Field k] {l : Type*} [Field l] [Algebra k l]
  {X : Type*} [AddCommGroup X] [Module k X]

private theorem discreteTensorQuotient_range_eq (P : Submodule k X) :
    (TensorProduct.AlgebraTensorModule.lTensor (R := k) l l
      (P.subtype.restrictScalars k)).range = P.baseChange l := by
  congr 1

private def discreteTensorQuotientEquiv (P : Submodule k X) :
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

private theorem discreteTensorQuotientEquiv_norm_eq (ξ : NormFamily T X)
    (hN : ∀ ω ∈ T.Ωinf, IsRCLikeNormedField (T.ϕ ω).Completion)
    (hi : ∃ a : k, a ^ 2 = -1) (P : Submodule k X)
    (x : T.ParameterSpaceExtension l) (z : x.abv.Completion ⊗[l] (l ⊗[k] (X ⧸ P))) :
    ((ξ.scalarExtension (L := l)).quotient (P.baseChange l)).norm x
        ((discreteTensorQuotientEquiv (l := l) P).toLinearMap.baseChange x.abv.Completion z) =
      ((ξ.quotient P).scalarExtension (L := l)).norm x z := by
  let e := discreteTensorQuotientEquiv (l := l) P
  let η := ξ.scalarExtension (L := l)
  let ω : (T.algebraicExtension l).Ω := x
  change ((T.algebraicExtension l).ϕ ω).Completion ⊗[l] (l ⊗[k] (X ⧸ P)) at z
  have hc := η.pushforward_comp_norm (P.mkQ.baseChange l)
    (LinearMap.baseChange_surjective l P.mkQ_surjective) e.toLinearMap e.surjective ω
      (e.toLinearMap.baseChange ((T.algebraicExtension l).ϕ ω).Completion z)
  dsimp only [e] at hc
  simp only [discreteTensorQuotientEquiv_comp_mkQ] at hc
  have ht := (η.pushforward (P.mkQ.baseChange l)
    (LinearMap.baseChange_surjective l P.mkQ_surjective)).pushforward_norm_of_injective
    e.toLinearMap e.surjective e.injective ω z
  exact (hc.symm.trans ht).trans
    (ξ.scalarExtension_pushforward_norm_eq_of_sqrt_neg_one hN hi P.mkQ P.mkQ_surjective x z)

end TensorQuotient

/-- The canonical place tower transport commutes with genuine quotient
norms on the identical completed fibre. -/
theorem towerPullback_quotient {X : Type*} [AddCommGroup X] [Module L X]
    [FiniteDimensional L X] (ξ : NormFamily (S.algebraicExtension L) X)
    (F : IntermediateField K L) (A : Submodule L X) :
    (ξ.towerPullback F).quotient A = (ξ.quotient A).towerPullback F := by
  ext x z
  rfl

private theorem discreteQuotient_cancel_norm_eq (ξ : NormFamily S E)
    (F : AdelicStructure.FiniteIntermediateField K L)
    (P : Submodule L (L ⊗[F] (F ⊗[K] E)))
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (z : x.abv.Completion ⊗[L] ((L ⊗[F] (F ⊗[K] E)) ⧸ P)) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := P.map c.toLinearMap
    let q := Submodule.Quotient.equiv P A c rfl
    (((ξ.scalarExtension (L := L)).towerPullback F.toIntermediateField).quotient A).norm x
      (q.toLinearMap.baseChange x.abv.Completion z) =
      (((ξ.scalarExtension (L := F)).scalarExtension (L := L)).quotient P).norm x z := by
  intro c A q
  have h := quotientEquiv_norm_eq (k := L)
    (T := (S.algebraicExtension F).algebraicExtension L)
    (X := L ⊗[F] (F ⊗[K] E)) (Y := L ⊗[K] E)
    ((ξ.scalarExtension (L := F)).scalarExtension (L := L))
    ((ξ.scalarExtension (L := L)).towerPullback F.toIntermediateField) x c P
    (fun t => (ξ.scalarExtension_trans x t).symm) z
  dsimp only at h
  exact h

/-- The native quotient norm is the extension of an actual native quotient
over a complexifying finite field, on every completed vector. -/
theorem scalarExtension_quotient_finiteStage_norm_eq (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
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
  have ht := ξ.discreteQuotient_cancel_norm_eq F (B.baseChange L) x
    (d.toLinearMap.baseChange x.abv.Completion z)
  dsimp only at ht
  rw [towerPullback_quotient] at ht
  exact ht.trans
    ((ξ.scalarExtension (L := F)).discreteTensorQuotientEquiv_norm_eq
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN) hi B x z)

variable [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- Every actual native target quotient has produced primal measurability
over a countable discrete original base. No target regularity is assumed. -/
theorem scalarExtension_quotient_isMeasurable_of_countable_discrete (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
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
  let θ := (ξ.scalarExtension (L := L)).quotient A
  have hm : η.IsMeasurable :=
    ((ξ.scalarExtension (L := F)).quotient (B 0)).scalarExtension_isMeasurable_of_countable_discrete
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN)
  intro y
  let τ := (AdelicStructure.Algebraic.towerMeasurableEquiv S F.toIntermediateField).symm
  have hnorm : (fun x : (S.algebraicExtension L).Ω =>
      θ.norm x ((1 : x.abv.Completion) ⊗ₜ[L] y)) =
      (fun x : (S.algebraicExtension L).Ω =>
        η.norm (τ x) ((1 : (τ x).abv.Completion) ⊗ₜ[L] d.symm (q.symm y))) := by
    funext x
    have h := ξ.scalarExtension_quotient_finiteStage_norm_eq hN F hi (B 0) (τ x)
      ((1 : (τ x).abv.Completion) ⊗ₜ[L] d.symm (q.symm y))
    have hd : d.toLinearMap.baseChange (τ x).abv.Completion
        ((1 : (τ x).abv.Completion) ⊗ₜ[L] d.symm (q.symm y)) =
        (1 : (τ x).abv.Completion) ⊗ₜ[L] q.symm y := by
      simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, d.apply_symm_apply]
    have hq : q.toLinearMap.baseChange (τ x).abv.Completion
        ((1 : (τ x).abv.Completion) ⊗ₜ[L] q.symm y) =
        (1 : (τ x).abv.Completion) ⊗ₜ[L] y := by
      simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, q.apply_symm_apply]
    have hv := congrArg (q.toLinearMap.baseChange (τ x).abv.Completion) hd
    have hn := congrArg (fun z : (τ x).abv.Completion ⊗[L] ((L ⊗[K] E) ⧸ A) =>
      θ.norm x z) (hv.trans hq)
    exact hn.symm.trans h
  change Measurable (fun x : (S.algebraicExtension L).Ω =>
    θ.norm x ((1 : x.abv.Completion) ⊗ₜ[L] y))
  rw [hnorm]
  exact (hm (d.symm (q.symm y))).comp τ.measurable

end NormFamily

namespace AdelicVectorBundle
variable [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- The genuine native target quotient bundle, with primal measurability
produced from finite descent and completed norm transport. -/
def scalarExtensionQuotientOfCountableDiscreteBase (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    AdelicVectorBundle (S.algebraicExtension L) ((L ⊗[K] E) ⧸ A) :=
  (V.scalarExtensionOfCountableDiscreteBase (L := L) hN).quotient A
    (V.toNormFamily.scalarExtension_quotient_isMeasurable_of_countable_discrete hN A)

@[simp]
theorem scalarExtensionQuotientOfCountableDiscreteBase_toNormFamily
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    (V.scalarExtensionQuotientOfCountableDiscreteBase (L := L) hN A).toNormFamily =
      (V.toNormFamily.scalarExtension (L := L)).quotient A := rfl

end AdelicVectorBundle
end ArakelovGeometry

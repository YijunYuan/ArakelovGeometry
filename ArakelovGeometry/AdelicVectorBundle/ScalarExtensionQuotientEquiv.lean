/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteQuotient

/-!
# Canonical scalar-extension quotient equivalences

The tensor quotient equivalence and tower cancellation give a public canonical
map from the extension of a finite-stage quotient to the prescribed native
quotient. Its completed norm identity consumes the genuine finite-stage
quotient norm theorem, without additional norm or measurability hypotheses.
-/

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v w wE

section TensorQuotient
variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
  {E : Type*} [AddCommGroup E] [Module K E]

private theorem tensorQuotient_range_eq (B : Submodule K E) :
    (TensorProduct.AlgebraTensorModule.lTensor (R := K) L L
      (B.subtype.restrictScalars K)).range = B.baseChange L := by
  congr 1

/-- The canonical tensor quotient map, with its kernel identified with the
actual base-changed subspace. -/
def tensorQuotientBaseChangeEquiv (B : Submodule K E) :
    (L ⊗[K] (E ⧸ B)) ≃ₗ[L] ((L ⊗[K] E) ⧸ B.baseChange L) :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := K) L K L B).trans
    (Submodule.quotEquivOfEq _ _ (tensorQuotient_range_eq B))

/-- The canonical equivalence commutes with the actual quotient maps on every
rational tensor. -/
theorem tensorQuotientBaseChangeEquiv_comp_mkQ (B : Submodule K E) :
    (tensorQuotientBaseChangeEquiv (L := L) B).toLinearMap.comp (B.mkQ.baseChange L) =
      (B.baseChange L).mkQ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a y
  rfl

end TensorQuotient

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  {E : Type wE} [AddCommGroup E] [Module K E]

/-- The canonical equivalence from an extended finite-stage quotient to the
native quotient by its literal image under tower cancellation. -/
def finiteStageQuotientEquiv (F : AdelicStructure.FiniteIntermediateField K L)
    (B : Submodule F (F ⊗[K] E)) :
    (L ⊗[F] ((F ⊗[K] E) ⧸ B)) ≃ₗ[L]
      ((L ⊗[K] E) ⧸ ((B.baseChange L).map
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap)) :=
  (tensorQuotientBaseChangeEquiv (L := L) B).trans
    (Submodule.Quotient.equiv _ _
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E) rfl)

/-- The finite-stage quotient equivalence intertwines the quotient maps with
actual tower cancellation, on all rational tensors. -/
theorem finiteStageQuotientEquiv_comp_mkQ
    (F : AdelicStructure.FiniteIntermediateField K L) (B : Submodule F (F ⊗[K] E)) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (B.baseChange L).map c.toLinearMap
    (finiteStageQuotientEquiv F B).toLinearMap.comp (B.mkQ.baseChange L) =
      A.mkQ.comp c.toLinearMap := by
  intro c A
  apply TensorProduct.AlgebraTensorModule.ext
  intro a y
  rfl

namespace NormFamily
variable {S : AdelicStructure.{u, v} K} [Algebra.IsAlgebraic K L]
  [FiniteDimensional K E]

/-- The produced canonical finite-stage quotient equivalence is an isometry
on every completed vector. The square-root and normalization hypotheses are
explicit; no measurability or original finite-place ultrametricity is assumed. -/
theorem scalarExtension_quotient_finiteStage_equiv_norm_eq (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (B : Submodule F (F ⊗[K] E))
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (z : x.abv.Completion ⊗[L] (L ⊗[F] ((F ⊗[K] E) ⧸ B))) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (B.baseChange L).map c.toLinearMap
    ((ξ.scalarExtension (L := L)).quotient A).norm (scalarExtensionTowerPlace x)
      ((finiteStageQuotientEquiv F B).toLinearMap.baseChange x.abv.Completion z) =
      (((ξ.scalarExtension (L := F)).quotient B).scalarExtension (L := L)).norm x z := by
  intro c A
  let d := tensorQuotientBaseChangeEquiv (L := L) B
  let q := Submodule.Quotient.equiv (B.baseChange L) A c rfl
  have h := ξ.scalarExtension_quotient_finiteStage_norm_eq hN F hi B x z
  change ((ξ.scalarExtension (L := L)).quotient A).norm (scalarExtensionTowerPlace x)
      (q.toLinearMap.baseChange x.abv.Completion
        (d.toLinearMap.baseChange x.abv.Completion z)) = _ at h
  have hv : (finiteStageQuotientEquiv F B).toLinearMap.baseChange x.abv.Completion z =
      q.toLinearMap.baseChange x.abv.Completion
        (d.toLinearMap.baseChange x.abv.Completion z) := by
    exact congrArg (fun f : _ →ₗ[x.abv.Completion] _ => f z)
      (LinearMap.baseChange_comp d.toLinearMap q.toLinearMap)
  exact (congrArg
    (fun t : x.abv.Completion ⊗[L] ((L ⊗[K] E) ⧸ A) =>
      ((ξ.scalarExtension (L := L)).quotient A).norm (scalarExtensionTowerPlace x) t)
    hv).trans h

end NormFamily
end ArakelovGeometry

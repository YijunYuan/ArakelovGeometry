/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTowerDeterminantDegree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionBundle
import ArakelovGeometry.AdelicVectorBundle.AlgebraicClosureApproximation
import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminantIsometry
import ArakelovGeometry.AdelicVectorBundle.DegreeIsometryDual
import ArakelovGeometry.AdelicVectorBundle.Slopes
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteQuotient

/-!
# Actual native subquotients through a scalar-extension tower

The canonical tensor associator transports arbitrary native subquotients, their
completed norms through the genuine place tower.
-/

set_option maxSynthPendingDepth 3

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
variable {K M E : Type*} [Field K] [Field M] [Algebra K M]
  [Algebra.IsAlgebraic K M] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {S : AdelicStructure K}

/-- The tensor associator induces the canonical map on every native quotient
of a native subspace of the iterated scalar extension. -/
def scalarExtensionTowerSubquotientEquiv (F : IntermediateField K M)
    (B : Submodule M (M ⊗[F] (F ⊗[K] E))) (U : Submodule M B) :
    (B ⧸ U) ≃ₗ[M]
      ((B.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).toLinearMap) ⧸
        U.map ((TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).submoduleMap
          B).toLinearMap) :=
  Submodule.Quotient.equiv U _
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).submoduleMap B) rfl

namespace NormFamily

/-- Actual native restricted quotient norms after iterated scalar extension. -/
def scalarExtensionTowerSubquotient (ξ : NormFamily S E) (F : IntermediateField K M)
    (B : Submodule M (M ⊗[F] (F ⊗[K] E))) (U : Submodule M B) :
    NormFamily ((S.algebraicExtension F).algebraicExtension M) (B ⧸ U) :=
  (((ξ.scalarExtension (L := F)).scalarExtension (L := M)).restrict B).quotient U

/-- The actual direct native norms on the associator image of a subquotient. -/
def scalarExtensionTowerImageSubquotient (ξ : NormFamily S E) (F : IntermediateField K M)
    (B : Submodule M (M ⊗[F] (F ⊗[K] E))) (U : Submodule M B) :
    NormFamily (S.algebraicExtension M)
      ((B.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).toLinearMap) ⧸
        U.map ((TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).submoduleMap
          B).toLinearMap) :=
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E
  ((ξ.scalarExtension (L := M)).restrict (B.map c.toLinearMap)).quotient
    (U.map (c.submoduleMap B).toLinearMap)

private theorem nativeTowerPullback_restrict
    {X : Type*} [AddCommGroup X] [Module M X]
    (ξ : NormFamily (S.algebraicExtension M) X) (F : IntermediateField K M)
    (B : Submodule M X) :
    (ξ.towerPullback F).restrict B = (ξ.restrict B).towerPullback F := by
  ext x z
  rfl

private theorem nativeTower_subquotient_norm_eq
    (F : IntermediateField K M)
    {X Y : Type*} [AddCommGroup X] [Module M X] [FiniteDimensional M X]
    [AddCommGroup Y] [Module M Y] [FiniteDimensional M Y]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension M) X)
    (θ : NormFamily (S.algebraicExtension M) Y) (e : X ≃ₗ[M] Y)
    (B : Submodule M X) (U : Submodule M B)
    (x : ((S.algebraicExtension F).algebraicExtension M).Ω)
    (he : ∀ t, θ.norm (scalarExtensionTowerPlace x)
      (e.toLinearMap.baseChange
        (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion t) =
        η.norm x t)
    (z : (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion ⊗[M] (B ⧸ U)) :
    ((((θ.restrict (B.map e.toLinearMap)).quotient
      (U.map (e.submoduleMap B).toLinearMap)).towerPullback F).norm x)
        ((Submodule.Quotient.equiv U (U.map (e.submoduleMap B).toLinearMap)
          (e.submoduleMap B) rfl).toLinearMap.baseChange
            (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion z) =
      ((η.restrict B).quotient U).norm x z := by
  have hr := η.restrict_map_equiv_norm_eq (θ.towerPullback F) e B x he
  have hq := (η.restrict B).quotient_map_equiv_norm_eq
    ((θ.towerPullback F).restrict (B.map e.toLinearMap)) (e.submoduleMap B) U x hr z
  rw [nativeTowerPullback_restrict, towerPullback_quotient] at hq
  exact hq


private theorem nativeTower_subquotient_pullback_eq
    (F : IntermediateField K M)
    {X Y : Type*} [AddCommGroup X] [Module M X] [FiniteDimensional M X]
    [AddCommGroup Y] [Module M Y] [FiniteDimensional M Y]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension M) X)
    (θ : NormFamily (S.algebraicExtension M) Y) (e : X ≃ₗ[M] Y)
    (B : Submodule M X) (U : Submodule M B)
    (he : ∀ x t, θ.norm (scalarExtensionTowerPlace x)
      (e.toLinearMap.baseChange
        (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion t) = η.norm x t) :
    (((θ.restrict (B.map e.toLinearMap)).quotient
      (U.map (e.submoduleMap B).toLinearMap)).towerPullback F).pullback
        (Submodule.Quotient.equiv U (U.map (e.submoduleMap B).toLinearMap)
          (e.submoduleMap B) rfl).toLinearMap
        (Submodule.Quotient.equiv U (U.map (e.submoduleMap B).toLinearMap)
          (e.submoduleMap B) rfl).injective = (η.restrict B).quotient U := by
  ext x z
  exact nativeTower_subquotient_norm_eq F η θ e B U x (he x) z

private theorem nativeTowerAmbient_norm_eq (ξ : NormFamily S E)
    (F : IntermediateField K M)
    (x : ((S.algebraicExtension F).algebraicExtension M).Ω)
    (z : (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion ⊗[M]
      (M ⊗[F] (F ⊗[K] E))) :
    (ξ.scalarExtension (L := M)).norm (scalarExtensionTowerPlace x)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).toLinearMap.baseChange
        (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion z) =
      ((ξ.scalarExtension (L := F)).scalarExtension (L := M)).norm x z :=
  (ξ.scalarExtension_trans x z).symm

private theorem nativeTowerActual_pullback_eq (ξ : NormFamily S E)
    (F : IntermediateField K M)
    (B : Submodule M (M ⊗[F] (F ⊗[K] E))) (U : Submodule M B) :
    ((ξ.scalarExtensionTowerImageSubquotient F B U).towerPullback F).pullback
      (scalarExtensionTowerSubquotientEquiv F B U).toLinearMap
      (scalarExtensionTowerSubquotientEquiv F B U).injective =
        ξ.scalarExtensionTowerSubquotient F B U := by
  dsimp only [scalarExtensionTowerImageSubquotient, scalarExtensionTowerSubquotient,
    scalarExtensionTowerSubquotientEquiv]
  exact nativeTower_subquotient_pullback_eq F
    ((ξ.scalarExtension (L := F)).scalarExtension (L := M)) (ξ.scalarExtension (L := M))
    (TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E) B U
    (fun x z => nativeTowerAmbient_norm_eq ξ F x z)

/-- Scalar transitivity transports every actual completed native subquotient
norm along the canonical tensor and place tower maps. -/
theorem scalarExtension_tower_subquotient_norm_eq (ξ : NormFamily S E)
    (F : IntermediateField K M)
    (B : Submodule M (M ⊗[F] (F ⊗[K] E))) (U : Submodule M B)
    (x : ((S.algebraicExtension F).algebraicExtension M).Ω)
    (z : (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion ⊗[M] (B ⧸ U)) :
    ((ξ.scalarExtensionTowerImageSubquotient F B U).towerPullback F).norm x
      ((scalarExtensionTowerSubquotientEquiv F B U).toLinearMap.baseChange
        (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion z) =
      (ξ.scalarExtensionTowerSubquotient F B U).norm x z := by
  exact congrArg
    (fun η : NormFamily ((S.algebraicExtension F).algebraicExtension M) (B ⧸ U) => η.norm x z)
    (nativeTowerActual_pullback_eq ξ F B U)

end NormFamily
end ArakelovGeometry

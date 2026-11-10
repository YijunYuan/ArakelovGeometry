/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerPlace
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Basic
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Tower.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual native subquotients through a scalar-extension tower

The canonical tensor associator transports arbitrary native subquotients, their
completed norms through the genuine place tower.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
variable {K M E : Type*} [Field K] [Field M] [Algebra K M]
  [Algebra.IsAlgebraic K M] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {S : AdelicStructure K}

/-- The tensor associator induces the canonical map on every native quotient
of a native subspace of the iterated scalar extension. -/
def scalarExtensionTowerSubquotientEquiv (F : Type*) [Field F] [Algebra K F] [Algebra F M]
    [IsScalarTower K F M]
    (B : Submodule M (M ⊗[F] (F ⊗[K] E))) (U : Submodule M B) :
    (B ⧸ U) ≃ₗ[M]
      ((B.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).toLinearMap) ⧸
        U.map ((TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).submoduleMap
          B).toLinearMap) :=
  Submodule.Quotient.equiv U _
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).submoduleMap B) rfl

namespace NormFamily

/-- Actual native restricted quotient norms after iterated scalar extension. -/
def scalarExtensionTowerSubquotient (ξ : NormFamily S E) (F : Type*) [Field F]
    [Algebra K F] [Algebra F M] [IsScalarTower K F M]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F M]
    (B : Submodule M (M ⊗[F] (F ⊗[K] E))) (U : Submodule M B) :
    NormFamily ((S.algebraicExtension F).algebraicExtension M) (B ⧸ U) :=
  (((ξ.scalarExtension (L := F)).scalarExtension (L := M)).restrict B).quotient U

/-- The actual direct native norms on the associator image of a subquotient. -/
def scalarExtensionTowerImageSubquotient (ξ : NormFamily S E) (F : Type*) [Field F]
    [Algebra K F] [Algebra F M] [IsScalarTower K F M]
    (B : Submodule M (M ⊗[F] (F ⊗[K] E))) (U : Submodule M B) :
    NormFamily (S.algebraicExtension M)
      ((B.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).toLinearMap) ⧸
        U.map ((TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).submoduleMap
          B).toLinearMap) :=
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E
  ((ξ.scalarExtension (L := M)).restrict (B.map c.toLinearMap)).quotient
    (U.map (c.submoduleMap B).toLinearMap)

private theorem subquotient_norm_eq_of_comp
    {k : Type*} [Field k] {T : AdelicStructure k}
    {X Y : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (η : NormFamily T X) (θ : NormFamily T Y) (e : X ≃ₗ[k] Y)
    (B : Submodule k X) (A : Submodule k Y) (eB : B ≃ₗ[k] A)
    (hB : A.subtype.comp eB.toLinearMap = e.toLinearMap.comp B.subtype)
    (U : Submodule k B) (V : Submodule k A) (q : (B ⧸ U) ≃ₗ[k] (A ⧸ V))
    (hq : q.toLinearMap.comp U.mkQ = V.mkQ.comp eB.toLinearMap)
    (x : T.Ω)
    (he : ∀ t, θ.norm x (e.toLinearMap.baseChange (T.ϕ x).Completion t) = η.norm x t)
    (z : (T.ϕ x).Completion ⊗[k] (B ⧸ U)) :
    ((θ.restrict A).quotient V).norm x
      (q.toLinearMap.baseChange (T.ϕ x).Completion z) =
        ((η.restrict B).quotient U).norm x z := by
  have hr (t : (T.ϕ x).Completion ⊗[k] B) :
      (θ.restrict A).norm x (eB.toLinearMap.baseChange (T.ϕ x).Completion t) =
        (η.restrict B).norm x t := by
    rw [restrict_norm, restrict_norm]
    have h := DFunLike.congr_fun
      (congrArg (fun f ↦ f.baseChange (T.ϕ x).Completion) hB) t
    simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at h
    rw [h]
    exact he _
  exact quotientEquiv_norm_eq_of_comp_eq (η.restrict B) (θ.restrict A) x eB U V q hq hr z

private theorem nativeTower_subquotient_norm_eq
    {F : Type*} [Field F] [Algebra K F] [Algebra F M] [IsScalarTower K F M]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F M]
    {X Y : Type*} [AddCommGroup X] [Module M X] [FiniteDimensional M X]
    [AddCommGroup Y] [Module M Y] [FiniteDimensional M Y]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension M) X)
    (θ : NormFamily (S.algebraicExtension M) Y) (e : X ≃ₗ[M] Y)
    (B : Submodule M X) (A : Submodule M Y) (eB : B ≃ₗ[M] A)
    (hB : A.subtype.comp eB.toLinearMap = e.toLinearMap.comp B.subtype)
    (U : Submodule M B) (V : Submodule M A) (q : (B ⧸ U) ≃ₗ[M] (A ⧸ V))
    (hq : q.toLinearMap.comp U.mkQ = V.mkQ.comp eB.toLinearMap)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) M)
    (he : ∀ t, θ.norm (scalarExtensionTowerPlace x)
      (e.toLinearMap.baseChange x.abv.Completion t) = η.norm x t)
    (z : x.abv.Completion ⊗[M] (B ⧸ U)) :
    ((θ.restrict A).quotient V).norm (scalarExtensionTowerPlace x)
      (q.toLinearMap.baseChange x.abv.Completion z) =
        ((η.restrict B).quotient U).norm x z := by
  let θt : NormFamily ((S.algebraicExtension F).algebraicExtension M) Y :=
    { norm x := θ.norm (scalarExtensionTowerPlace x)
      norm_eq_zero_iff x := θ.norm_eq_zero_iff (scalarExtensionTowerPlace x) }
  exact subquotient_norm_eq_of_comp η θt e B A eB hB U V q hq x he z

private theorem nativeTowerAmbient_norm_eq (ξ : NormFamily S E)
    (F : Type*) [Field F] [Algebra K F] [Algebra F M] [IsScalarTower K F M]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F M]
    (x : ((S.algebraicExtension F).algebraicExtension M).Ω)
    (z : (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion ⊗[M]
      (M ⊗[F] (F ⊗[K] E))) :
    (ξ.scalarExtension (L := M)).norm (scalarExtensionTowerPlace x)
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E).toLinearMap.baseChange
        (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion z) =
      ((ξ.scalarExtension (L := F)).scalarExtension (L := M)).norm x z :=
  (ξ.scalarExtension_trans x z).symm

/-- Scalar transitivity transports every actual completed native subquotient
norm along the canonical tensor and place tower maps. -/
theorem scalarExtension_tower_subquotient_norm_eq (ξ : NormFamily S E)
    (F : Type*) [Field F] [Algebra K F] [Algebra F M] [IsScalarTower K F M]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F M]
    (B : Submodule M (M ⊗[F] (F ⊗[K] E))) (U : Submodule M B)
    (x : ((S.algebraicExtension F).algebraicExtension M).Ω)
    (z : (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion ⊗[M] (B ⧸ U)) :
    (ξ.scalarExtensionTowerImageSubquotient F B U).norm (scalarExtensionTowerPlace x)
      ((scalarExtensionTowerSubquotientEquiv F B U).toLinearMap.baseChange
        (((S.algebraicExtension F).algebraicExtension M).ϕ x).Completion z) =
      (ξ.scalarExtensionTowerSubquotient F B U).norm x z := by
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F M M E
  let A := B.map c.toLinearMap
  let eB : B ≃ₗ[M] A := c.submoduleMap B
  let V := U.map eB.toLinearMap
  let q : (B ⧸ U) ≃ₗ[M] (A ⧸ V) := scalarExtensionTowerSubquotientEquiv F B U
  have hB : A.subtype.comp eB.toLinearMap = c.toLinearMap.comp B.subtype := rfl
  have hq : q.toLinearMap.comp U.mkQ = V.mkQ.comp eB.toLinearMap := by
    ext y
    rfl
  exact nativeTower_subquotient_norm_eq (K := K) (M := M) (S := S)
    (X := M ⊗[F] (F ⊗[K] E)) (Y := M ⊗[K] E) (F := F)
    ((ξ.scalarExtension (L := F)).scalarExtension (L := M)) (ξ.scalarExtension (L := M))
    c B A eB hB U V q hq x (nativeTowerAmbient_norm_eq ξ F x) z

end NormFamily
end ArakelovGeometry

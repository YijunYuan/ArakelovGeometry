/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.SubspaceQuotient
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.NativeSubquotientFiniteStage

import ArakelovGeometry.AdelicVectorBundle.Degree.IsometryDual
import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual dual isometries and strong native mixed subquotients

The existing canonical native mixed bundle already has produced primal and
dual measurability and domination. Its actual finite-stage isometry preserves
every completed dual norm, and ordinary scalar strong domination makes every
such actual native mixed bundle strongly adelic.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

private theorem nativeSubquotient_dual_norm_eq
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L]
    {X Y : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension L) X)
    (θ : NormFamily (S.algebraicExtension L) Y) (e : X ≃ₗ[L] Y)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (he : ∀ t, θ.norm (scalarExtensionTowerPlace x)
      (e.toLinearMap.baseChange x.abv.Completion t) = η.norm x t)
    (z : x.abv.Completion ⊗[L] Module.Dual L Y) :
    η.dual.norm x (e.dualMap.toLinearMap.baseChange x.abv.Completion z) =
      θ.dual.norm (scalarExtensionTowerPlace x) z := by
  let θ' : NormFamily ((S.algebraicExtension F).algebraicExtension L) Y :=
    { norm x := θ.norm (scalarExtensionTowerPlace x)
      norm_eq_zero_iff x := θ.norm_eq_zero_iff (scalarExtensionTowerPlace x) }
  exact η.dualEquiv_norm_eq_of_completed_isometry θ' x e he z

/-- The actual finite-stage subquotient equivalence preserves every completed
dual norm through its genuine transpose, with no original ultrametricity or
regularity hypothesis on the norm family. -/
theorem scalarExtension_subquotient_finiteStage_dual_norm_eq (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (P.baseChange L).map c.toLinearMap
    let B := (Q.baseChange L).map c.toLinearMap
    let e := finiteStageSubquotientEquiv (L := L) F P Q hPQ
    ∀ z : x.abv.Completion ⊗[L] Module.Dual L (B ⧸ A.comap B.subtype),
      ((((ξ.scalarExtension (L := F)).restrict Q).quotient
        (P.comap Q.subtype)).scalarExtension (L := L)).dual.norm x
          (e.dualMap.toLinearMap.baseChange x.abv.Completion z) =
      (((ξ.scalarExtension (L := L)).restrict B).quotient
        (A.comap B.subtype)).dual.norm (scalarExtensionTowerPlace x) z := by
  intro c A B e z
  exact nativeSubquotient_dual_norm_eq F
    ((((ξ.scalarExtension (L := F)).restrict Q).quotient
      (P.comap Q.subtype)).scalarExtension (L := L))
    (((ξ.scalarExtension (L := L)).restrict B).quotient (A.comap B.subtype)) e x
    (fun t ↦ ξ.scalarExtension_subquotient_finiteStage_norm_eq F hi P Q hPQ x t) z

end NormFamily
namespace AdelicVectorBundle
variable [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] [IsAlgClosed L]

/-- Every genuine native mixed quotient over the algebraic closure is strongly
adelic. The original bundle need not be strongly adelic or ultrametric, and no
regularity of the target place space is assumed. -/
theorem scalarExtensionSubspaceQuotientOfCountableDiscreteBase_isStronglyAdelic
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (B : Submodule L (L ⊗[K] V)) (T : Submodule L B) :
    (V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase B T).IsStronglyAdelic := by
  change (((V.toNormFamily.scalarExtension (L := L)).restrict B).quotient T).IsStronglyDominated
  have hs : (V.toNormFamily.scalarExtension (L := L)).IsStronglyDominated :=
    V.scalarExtensionOfCountableDiscreteBase_isStronglyAdelic
  have hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  exact (hs.restrict B (hS := ⟨hLN⟩)).quotient T (hS := ⟨hLN⟩)

end AdelicVectorBundle
end ArakelovGeometry

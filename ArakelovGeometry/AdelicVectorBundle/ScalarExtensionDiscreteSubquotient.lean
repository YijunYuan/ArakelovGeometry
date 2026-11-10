/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionSubspaceComplexDescent
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteBundle

/-!
# Actual subspaces over algebraic extensions of a countable discrete base

Complexifying finite-stage descent identifies native target restrictions with
extensions of the genuine native finite-stage restrictions on every completed
vector. The target parameter sigma algebra is not assumed discrete.
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

/-- Actual finite-stage restriction and direct native restriction agree on
all completed vectors through the canonical subspace tensor equivalence.
No original finite-place ultrametric hypothesis is needed after the first extension. -/
theorem scalarExtension_restrict_finiteStage_norm_eq (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (B : Submodule F (F ⊗[K] E))
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (z : x.abv.Completion ⊗[L] (L ⊗[F] B)) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let e := (Submodule.toBaseChange.toLinearEquiv L B).trans (c.submoduleMap (B.baseChange L))
    ((ξ.scalarExtension (L := L)).restrict ((B.baseChange L).map c.toLinearMap)).norm
      (scalarExtensionTowerPlace x) (e.toLinearMap.baseChange x.abv.Completion z) =
    (((ξ.scalarExtension (L := F)).restrict B).scalarExtension (L := L)).norm x z := by
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let e := (Submodule.toBaseChange.toLinearEquiv L B).trans (c.submoduleMap (B.baseChange L))
  have hc : ((B.baseChange L).map c.toLinearMap).subtype.comp e.toLinearMap =
      c.toLinearMap.comp (B.subtype.baseChange L) := by
    rfl
  have hz := DFunLike.congr_fun
    (congrArg (fun f => f.baseChange x.abv.Completion) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
  change (ξ.scalarExtension (L := L)).norm (scalarExtensionTowerPlace x)
    (((B.baseChange L).map c.toLinearMap).subtype.baseChange x.abv.Completion
      (e.toLinearMap.baseChange x.abv.Completion z)) = _
  rw [hz]
  exact (ξ.scalarExtension_trans x
    ((B.subtype.baseChange L).baseChange x.abv.Completion z)).symm.trans
    ((ξ.scalarExtension (L := F)).scalarExtension_pullback_norm_eq_of_sqrt_neg_one
      ξ.scalarExtension_isUltrametric
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN)
      hi B.subtype B.subtype_injective x z)

/-- Every finite actual target subspace family admits one produced complexifying
field and actual finite-stage native restrictions whose extended norms are
isometric to the prescribed native target restrictions on every completed vector. -/
theorem exists_complexFiniteStage_restriction_isometries [IsAlgClosed L]
    (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {ι : Type*} [Finite ι] (A : ι → Submodule L (L ⊗[K] E)) :
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ B : ι → Submodule F (F ⊗[K] E),
        (∀ i, Submodule.map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
          ((B i).baseChange L) = A i) ∧
        (∀ i, Module.finrank F (B i) = Module.finrank L (A i)) ∧
        ∀ i, ∃ e : (L ⊗[F] B i) ≃ₗ[L] A i,
          ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
            (z : x.abv.Completion ⊗[L] (L ⊗[F] B i)),
            ((ξ.scalarExtension (L := L)).restrict (A i)).norm
              (scalarExtensionTowerPlace x) (e.toLinearMap.baseChange x.abv.Completion z) =
            (((ξ.scalarExtension (L := F)).restrict (B i)).scalarExtension (L := L)).norm
              x z := by
  obtain ⟨F, hi, B, hB, hr, _⟩ := exists_complexFiniteStage_subspaces A
  refine ⟨F, hi, B, hB, hr, ?_⟩
  intro i
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let e₀ := (Submodule.toBaseChange.toLinearEquiv L (B i)).trans
    (c.submoduleMap ((B i).baseChange L))
  let e := e₀.trans (LinearEquiv.ofEq _ _ (hB i))
  refine ⟨e, ?_⟩
  intro x z
  have hc : (A i).subtype.comp e.toLinearMap =
      (((B i).baseChange L).map c.toLinearMap).subtype.comp e₀.toLinearMap := by
    rfl
  have hz := DFunLike.congr_fun
    (congrArg (fun f => f.baseChange x.abv.Completion) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
  exact (congrArg ((ξ.scalarExtension (L := L)).norm (scalarExtensionTowerPlace x)) hz).trans
    (ξ.scalarExtension_restrict_finiteStage_norm_eq hN F hi (B i) x z)

end NormFamily
end ArakelovGeometry

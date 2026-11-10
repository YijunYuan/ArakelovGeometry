/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerBasic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Dual.FiniteStage
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.FiniteStage.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Finite-stage descent of actual scalar dual norms

Canonical dual base change commutes with field-tower cancellation. Actual
completed dual norm transport then descends rational functional evaluations
to finite coordinate fields over a countable discrete parameter space.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

universe u v w wE

section Tower

variable {K : Type u} [Field K] {F : Type*} [Field F] [Algebra K F]
  {L : Type w} [Field L] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Extending an actual rational functional commutes with canonical tower cancellation. -/
theorem dualBaseChangeEquiv_tower_one_tmul (y : F ⊗[K] Module.Dual K E) :
    let d := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    d.dualMap (dualBaseChangeEquiv K L E
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L (Module.Dual K E)
        ((1 : L) ⊗ₜ[F] y))) =
      dualBaseChangeEquiv F L (F ⊗[K] E)
        ((1 : L) ⊗ₜ[F] dualBaseChangeEquiv K F E y) := by
  intro d
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | tmul a ℓ =>
    apply TensorProduct.AlgebraTensorModule.ext
    intro b t
    induction t using TensorProduct.inductionOn with
    | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]
    | tmul c e =>
      simp [d, LinearEquiv.dualMap_apply,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        dualBaseChangeEquiv_tmul_apply_tmul, Algebra.smul_def,
        IsScalarTower.algebraMap_apply K F L, mul_assoc, mul_left_comm, mul_comm]


end Tower

namespace NormFamily

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)

/-- Actual rational dual evaluations descend to their finite coordinate field. -/
theorem scalarExtension_dual_norm_finiteStage
    (F : AdelicStructure.FiniteIntermediateField K L)
    (x : S.ParameterSpaceExtension L) (y : F ⊗[K] Module.Dual K E) :
    (ξ.scalarExtension (L := L)).dual.norm x
      ((1 : x.abv.Completion) ⊗ₜ[L]
        dualBaseChangeEquiv K L E
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L (Module.Dual K E)
            ((1 : L) ⊗ₜ[F] y))) =
      (ξ.scalarExtension (L := F)).dual.norm
        (AdelicStructure.ParameterSpaceExtension.restrict S L x F)
        ((1 : (x.abv.under F).Completion) ⊗ₜ[F] dualBaseChangeEquiv K F E y) := by
  let xT : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L :=
    (AdelicStructure.Algebraic.towerMeasurableEquiv S F.1).symm x
  have he := (ξ.scalarExtension (L := F)).scalarExtension_dual_norm_rational_one_tmul
    xT (dualBaseChangeEquiv K F E y)
  have ht := ξ.scalarExtension_dual_trans (F := F) xT
    ((1 : xT.abv.Completion) ⊗ₜ[L]
      dualBaseChangeEquiv K L E
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L (Module.Dual K E)
          ((1 : L) ⊗ₜ[F] y)))
  dsimp only at ht
  rw [LinearMap.baseChange_tmul] at ht
  have ha := dualBaseChangeEquiv_tower_one_tmul (K := K) (L := L) y
  dsimp only at ha
  erw [ha] at ht
  exact ht.symm.trans he

/-- For an arbitrary algebraic extension, dual measurability follows from the
countable discrete original base by actual finite-coordinate descent. -/
theorem scalarExtension_dual_isMeasurable_of_countable_discrete
    [Countable S.Ω] [DiscreteMeasurableSpace S.Ω] :
    (ξ.scalarExtension (L := L)).dual.IsMeasurable := by
  intro ℓ
  obtain ⟨F, y, hy⟩ := exists_finiteStage_tensor_lift
    ((dualBaseChangeEquiv K L E).symm ℓ)
  have hℓ : dualBaseChangeEquiv K L E
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L (Module.Dual K E)
        ((1 : L) ⊗ₜ[F] y)) = ℓ := by
    rw [hy, LinearEquiv.apply_symm_apply]
  have hm := ξ.scalarExtension_dual_isMeasurable_of_finiteDimensional_of_countable_discrete
    (L := F)
  have hr : @Measurable (S.algebraicExtension L).Ω (S.algebraicExtension F).Ω
      (S.algebraicExtension L).instMeasurableSpaceΩ
      (S.algebraicExtension F).instMeasurableSpaceΩ
      (fun x => AdelicStructure.ParameterSpaceExtension.restrict S L x F) := by
    change @Measurable _ _ (AdelicStructure.Algebraic.projectiveMeasurableSpace S L)
      (AdelicStructure.Algebraic.projectiveMeasurableSpace S F) _
    rw [AdelicStructure.Algebraic.projectiveMeasurableSpace_eq,
      AdelicStructure.Algebraic.projectiveMeasurableSpace_eq]
    exact AdelicStructure.ParameterSpaceExtension.measurable_restrict S L F.1
  have he : (fun x : (S.algebraicExtension L).Ω =>
      (ξ.scalarExtension (L := L)).dual.norm x
        ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] ℓ)) =
      (fun x : (S.algebraicExtension L).Ω =>
        (ξ.scalarExtension (L := F)).dual.norm
          (AdelicStructure.ParameterSpaceExtension.restrict S L x F)
          ((1 : (x.abv.under F).Completion) ⊗ₜ[F] dualBaseChangeEquiv K F E y)) := by
    funext x
    rw [← hℓ]
    exact ξ.scalarExtension_dual_norm_finiteStage F x y
  rw [he]
  exact (hm (dualBaseChangeEquiv K F E y)).comp hr

end NormFamily

end ArakelovGeometry

end

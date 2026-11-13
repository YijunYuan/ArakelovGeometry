/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Restricted coordinate maxima at arbitrarily chosen extending places

The actual completed restriction in Chen–Moriwaki, Proposition 4.1.15.
Choices of extending places carry no measurability hypothesis.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u w wE

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {L : Type w} [Field L] [Algebra K L]
  {E : Type wE} [AddCommGroup E] [Module K E]

/-- The canonical injection of a completed base fibre into a chosen extended
completed fibre, with the latter in its actual tensor-product coordinates. -/
def chosenExtensionMap (ω : S.Ω) (w : AbsoluteValue L ℝ)
    (hw : w.under K = S.ϕ ω) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) w hw
    (S.ϕ ω).Completion ⊗[K] E →ₗ[(S.ϕ ω).Completion]
      w.Completion ⊗[L] (L ⊗[K] E) := by
  letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) w hw
  exact ((completedScalarExtensionEquiv E (S.ϕ ω) w hw).symm.restrictScalars
    (S.ϕ ω).Completion).toLinearMap.comp
      (TensorProduct.mk (S.ϕ ω).Completion w.Completion
        ((S.ϕ ω).Completion ⊗[K] E) 1)

/-- The completed-fibre map used for restriction is injective. -/
theorem chosenExtensionMap_injective (ω : S.Ω) (w : AbsoluteValue L ℝ)
    (hw : w.under K = S.ϕ ω) :
    Function.Injective (chosenExtensionMap (E := E) ω w hw) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) w hw
  let : FaithfulSMul (S.ϕ ω).Completion w.Completion :=
    (faithfulSMul_iff_algebraMap_injective (S.ϕ ω).Completion w.Completion).mpr
      (algebraMap (S.ϕ ω).Completion w.Completion).injective
  exact (completedScalarExtensionEquiv E (S.ϕ ω) w hw).symm.injective.comp
    (Module.Flat.tensorProduct_mk_injective (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E) w.Completion)

/-- A base completed scalar and rational vector map to their literal
extended scalar tensor. -/
theorem chosenExtensionMap_tmul (ω : S.Ω) (w : AbsoluteValue L ℝ)
    (hw : w.under K = S.ϕ ω) (a : (S.ϕ ω).Completion) (x : E) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) w hw
    chosenExtensionMap ω w hw (a ⊗ₜ[K] x) =
      algebraMap (S.ϕ ω).Completion w.Completion a ⊗ₜ[L] ((1 : L) ⊗ₜ[K] x) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) w hw
  simp only [chosenExtensionMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_apply, TensorProduct.mk_apply,
    completedScalarExtensionEquiv_symm_tmul, mul_one]

/-- A supremum norm in an arbitrary algebraic basis, restricted to the
original completed fibre. No measurability of the place choices is assumed. -/
def ofChosenAlgebraicBasis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι L (L ⊗[K] E))
    (w : S.Ω → AbsoluteValue L ℝ) (hw : ∀ ω, (w ω).under K = S.ϕ ω) :
    NormFamily S E where
  norm ω := by
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) (w ω) (hw ω)
    exact ((normSeminorm (w ω).Completion (ι → (w ω).Completion)).restrictScalars
      (S.ϕ ω).Completion).comp
        (((b.baseChange (w ω).Completion).equivFun.restrictScalars
          (S.ϕ ω).Completion).toLinearMap.comp (chosenExtensionMap ω (w ω) (hw ω)))
  norm_eq_zero_iff ω z := by
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) (w ω) (hw ω)
    change ‖(b.baseChange (w ω).Completion).equivFun
      (chosenExtensionMap ω (w ω) (hw ω) z)‖ = 0 ↔ z = 0
    rw [norm_eq_zero, LinearEquiv.map_eq_zero_iff]
    exact (chosenExtensionMap_injective ω (w ω) (hw ω)).eq_iff' (map_zero _)

/-- The restricted family is the literal completed coordinate maximum. -/
theorem ofChosenAlgebraicBasis_norm {ι : Type*} [Fintype ι]
    (b : Module.Basis ι L (L ⊗[K] E))
    (w : S.Ω → AbsoluteValue L ℝ) (hw : ∀ ω, (w ω).under K = S.ϕ ω)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] E) :
    (ofChosenAlgebraicBasis b w hw).norm ω z =
      ‖(b.baseChange (w ω).Completion).equivFun
        (chosenExtensionMap ω (w ω) (hw ω) z)‖ := rfl

end ArakelovGeometry.NormFamily

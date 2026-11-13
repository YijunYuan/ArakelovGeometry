/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Dual.Basic

import ArakelovGeometry.Analysis.Dual.ArchimedeanDual
import ArakelovGeometry.Analysis.Dual.UltrametricDual
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Bidual norms on completed fibres

The canonical evaluation map is an isometry at every ultrametric fibre.
The lower norm bound consumes approximate extension of actual functionals;
the upper bound is the evaluation contraction from the dual construction.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The completed bidual norm equals the original norm at any ultrametric fibre. -/
theorem dual_dual_norm_eval_eq_of_ultrametric (ξ : NormFamily S E) (ω : S.Ω)
    (hξ : ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y))
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.dual.dual.norm ω ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion x) =
      ξ.norm ω x := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  have : IsUltrametricDist ((S.ϕ ω).Completion ⊗[K] E) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm hξ
  apply le_antisymm (ξ.dual_dual_norm_eval_le ω x)
  apply norm_le_of_forall_linearMap_apply_le (L := (S.ϕ ω).Completion) (x := x)
    (ξ.dual.dual.norm_nonneg ω _)
  intro f
  let z := (dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm f
  have hz : dualBaseChangeEquiv K (S.ϕ ω).Completion E z = f :=
    (dualBaseChangeEquiv K (S.ϕ ω).Completion E).apply_symm_apply _
  have hzn : ξ.dual.norm ω z = linearMapOperatorSeminorm f := by
    change linearMapOperatorSeminorm (dualBaseChangeEquiv K (S.ϕ ω).Completion E z) = _
    rw [hz]
  have hb := ξ.dual.norm_dual_apply_le ω
    ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion x) z
  simpa only [dualBaseChangeEquiv_eval, LinearEquiv.dualMap_apply,
    Module.Dual.eval_apply, hz, hzn, mul_comm] using hb

/-- An ultrametric norm family agrees with its bidual at every
non-Archimedean place, including trivially valued places. -/
theorem IsUltrametricAtFinitePlaces.dual_dual_norm_eval
    {ξ : NormFamily S E} (hξ : ξ.IsUltrametricAtFinitePlaces)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.dual.dual.norm ω ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion x) =
      ξ.norm ω x :=
  ξ.dual_dual_norm_eval_eq_of_ultrametric ω (hξ ω hω) x

/-- Biduality is isometric at a fibre whose canonical completed-field norm
is the usual real or complex norm. -/
theorem dual_dual_norm_eval_eq_of_isRCLike (ξ : NormFamily S E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.dual.dual.norm ω ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion x) =
      ξ.norm ω x := by
  let := hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  apply le_antisymm (ξ.dual_dual_norm_eval_le ω x)
  apply norm_le_of_forall_linearMap_apply_le_archimedean
    (L := (S.ϕ ω).Completion) (x := x) (ξ.dual.dual.norm_nonneg ω _)
  intro f
  let z := (dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm f
  have hz : dualBaseChangeEquiv K (S.ϕ ω).Completion E z = f :=
    (dualBaseChangeEquiv K (S.ϕ ω).Completion E).apply_symm_apply _
  have hzn : ξ.dual.norm ω z = linearMapOperatorSeminorm f := by
    change linearMapOperatorSeminorm (dualBaseChangeEquiv K (S.ϕ ω).Completion E z) = _
    rw [hz]
  have hb := ξ.dual.norm_dual_apply_le ω
    ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion x) z
  simpa only [dualBaseChangeEquiv_eval, LinearEquiv.dualMap_apply,
    Module.Dual.eval_apply, hz, hzn, mul_comm] using hb

/-- With the source's usual Archimedean absolute values, an ultrametric norm
family equals its bidual under canonical evaluation. The normalization of the
actual completed fields is an explicit hypothesis. -/
theorem dual_dual_pullback_eq (ξ : NormFamily S E) [hξ : ξ.IsUltrametricAtFinitePlaces]
    [hS : S.IsArchimedeanNormalized] :
    ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K) = ξ := by
  ext ω x
  by_cases hω : ω ∈ S.Ωfin
  · exact hξ.dual_dual_norm_eval ω hω x
  · exact ξ.dual_dual_norm_eval_eq_of_isRCLike ω (hS ω hω) x

end ArakelovGeometry.NormFamily

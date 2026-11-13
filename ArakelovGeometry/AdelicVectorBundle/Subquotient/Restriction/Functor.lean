/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic

import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Canonical isometries for nested restrictions

Restriction through an intermediate rational subspace has the same actual
completed norm as direct restriction. Canonical subspace identifications
therefore preserve actual degrees, including zero and repeated terms of a flag.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E]

namespace NormFamily

/-- Nested and direct restrictions agree on every actual completed vector
under the canonical equivalence of the rational subspaces. -/
theorem restrict_restrict_norm_eq (ξ : NormFamily S E) (U W : Submodule K E)
    (h : U ≤ W) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] U.comap W.subtype) :
    ((ξ.restrict W).restrict (U.comap W.subtype)).norm ω z =
      (ξ.restrict U).norm ω
        ((Submodule.comapSubtypeEquivOfLe h).toLinearMap.baseChange
          (S.ϕ ω).Completion z) := by
  have he : U.subtype.comp (Submodule.comapSubtypeEquivOfLe h).toLinearMap =
      W.subtype.comp (U.comap W.subtype).subtype := by
    apply LinearMap.ext
    intro x
    rfl
  have hz := DFunLike.congr_fun
    (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) he) z
  simp only [restrict_norm]
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using
    (congrArg (ξ.norm ω) hz).symm

/-- The actual nested norm family is precisely the pullback of the direct
restriction along the existing canonical subspace equivalence. -/
theorem restrict_restrict (ξ : NormFamily S E) (U W : Submodule K E) (h : U ≤ W) :
    (ξ.restrict W).restrict (U.comap W.subtype) =
      (ξ.restrict U).pullback (Submodule.comapSubtypeEquivOfLe h).toLinearMap
        (Submodule.comapSubtypeEquivOfLe h).injective := by
  ext ω z
  simpa only [pullback_norm] using ξ.restrict_restrict_norm_eq U W h ω z

/-- Restriction to the total rational subspace preserves every actual
completed norm under its canonical equivalence with the ambient space. -/
theorem restrict_top_norm_eq (ξ : NormFamily S E) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⊤ : Submodule K E)) :
    (ξ.restrict ⊤).norm ω z = ξ.norm ω
      ((Submodule.topEquiv : (⊤ : Submodule K E) ≃ₗ[K] E).toLinearMap.baseChange
        (S.ϕ ω).Completion z) := rfl

end NormFamily

namespace AdelicVectorBundle

variable [FiniteDimensional K E]

/-- Nested restriction and direct restriction have the same actual degree. -/
theorem degree_restrict_restrict [S.IsProper] (V : AdelicVectorBundle S)
    (U W : Submodule K V) (h : U ≤ W)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    ((V.restrictOfNormMeasurability W).restrictOfNormMeasurability
      (U.comap W.subtype)).degree =
      (V.restrictOfNormMeasurability U).degree := by
  apply degree_eq_of_completed_isometry _ _ (Submodule.comapSubtypeEquivOfLe h)
  intro ω z
  exact (V.toNormFamily.restrict_restrict_norm_eq U W h ω z).symm

/-- The actual total-subspace restriction has the ambient bundle degree. -/
theorem degree_restrict_top [S.IsProper] (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.restrictOfNormMeasurability ⊤).degree = V.degree := by
  apply degree_eq_of_completed_isometry _ _ Submodule.topEquiv
  intro ω z
  exact (V.toNormFamily.restrict_top_norm_eq ω z).symm

end AdelicVectorBundle

end ArakelovGeometry

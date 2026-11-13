/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Strong

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
import ArakelovGeometry.AdelicVectorBundle.Tensor.Domination
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Domination of exterior powers and determinants

Source Proposition 4.1.19(6) follows from the actual mixed tensor norm and
strong quotient construction. Degree zero and powers above dimension are
included by the same canonical quotient construction.
-/

@[expose] public section

namespace ArakelovGeometry.NormFamily

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily S E}

/-- Every actual exterior-power family of a dominated family is strongly dominated. -/
theorem IsDominated.strong_exteriorPower (hξ : ξ.IsDominated) (n : ℕ)
    [hS : S.IsArchimedeanNormalized] :
    (ξ.exteriorPower n).IsStronglyDominated :=
  (IsDominated.strong_mixedTensor (fun _ : Fin n ↦ ξ) (fun _ ↦ hξ)
    (S.v_Ωinf_lt_top_of_isRCLike)).pushforward
      (tensorToExterior K E n) (tensorToExterior_surjective K E n)

/-- Exterior-power domination, for arbitrary nonnegative degree. -/
theorem IsDominated.exteriorPower (hξ : ξ.IsDominated) (n : ℕ)
    [hS : S.IsArchimedeanNormalized] :
    (ξ.exteriorPower n).IsDominated := (hξ.strong_exteriorPower n).isDominated

/-- The actual projective determinant quotient is strongly dominated, also in rank zero. -/
theorem IsDominated.strong_determinant (hξ : ξ.IsDominated)
    [hS : S.IsArchimedeanNormalized] :
    ξ.determinant.IsStronglyDominated := by
  rw [ξ.determinant_eq_exteriorPower]
  exact hξ.strong_exteriorPower (Module.finrank K E)

/-- Domination of the genuine determinant line norm family. -/
theorem IsDominated.determinant (hξ : ξ.IsDominated)
    [hS : S.IsArchimedeanNormalized] :
    ξ.determinant.IsDominated := (hξ.strong_determinant).isDominated

end ArakelovGeometry.NormFamily

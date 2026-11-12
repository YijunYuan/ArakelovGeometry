/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic
public import ArakelovGeometry.AdelicVectorBundle.Determinant.DualBaseChange

import ArakelovGeometry.AdelicVectorBundle.Determinant.Duality
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Degree duality for Hermitian adelic bundles

The actual canonical determinant-dual isometry and the degree formula for
dual lines prove Proposition 4.3.8, including the zero-dimensional bundle.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Dualizing a Hermitian adelic bundle negates its Arakelov degree. -/
theorem degree_dualOfMeasurableBase [S.IsProper] (V : AdelicVectorBundle S E)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.IsHermitian] :
    (V.dualOfMeasurableBase).degree = -V.degree := by
  let D := V.determinantOfMeasurableBase
  have hD : D.IsLine := V.determinantOfMeasurableBase_isLine
  calc
    (V.dualOfMeasurableBase).degree =
        (D.dualLine (hV := hD)).lineDegree (hV := (D.dualLine_isLine (hV := hD))) := by
      apply lineDegree_eq_of_norm_rational_eq _ _ (determinantDualEquiv K E)
      intro ω x
      change V.toNormFamily.dual.determinant.norm ω (1 ⊗ₜ[K] x) =
        V.toNormFamily.determinant.dual.norm ω
          (1 ⊗ₜ[K] determinantDualEquiv K E x)
      simpa only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe] using
        hV.determinant_dual_norm V.toNormFamily ω (1 ⊗ₜ[K] x)
    _ = -V.degree := lineDegree_dualLine D (hV := hD)

end ArakelovGeometry.AdelicVectorBundle

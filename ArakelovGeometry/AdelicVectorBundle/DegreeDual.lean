/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.Degree
import ArakelovGeometry.AdelicVectorBundle.DeterminantDuality

/-!
# Degree duality for Hermitian adelic bundles

The actual canonical determinant-dual isometry and the degree formula for
dual lines prove Proposition 4.3.8, including the zero-dimensional bundle.
-/

open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Dualizing a Hermitian adelic bundle negates its Arakelov degree. -/
theorem degree_dualOfMeasurableBase [S.IsProper] (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.IsHermitian hN) :
    (V.dualOfMeasurableBase hS).degree hS hN = -V.degree hS hN := by
  let D := V.determinantOfMeasurableBase hS hN
  have hD : D.IsLine := V.determinantOfMeasurableBase_isLine hS hN
  calc
    (V.dualOfMeasurableBase hS).degree hS hN =
        (D.dualLine hD).lineDegree (D.dualLine_isLine hD) := by
      apply lineDegree_eq_of_norm_rational_eq _ _ _ _ (determinantDualEquiv K E)
      intro ω x
      change V.toNormFamily.dual.determinant.norm ω (1 ⊗ₜ[K] x) =
        V.toNormFamily.determinant.dual.norm ω
          (1 ⊗ₜ[K] determinantDualEquiv K E x)
      simpa only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe] using
        hV.determinant_dual_norm V.toNormFamily ω (1 ⊗ₜ[K] x)
    _ = -V.degree hS hN := lineDegree_dualLine D hD

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DirectSum
public import ArakelovGeometry.AdelicVectorBundle.Measurable
public import ArakelovGeometry.Analysis.NormShapeMeasurable

/-!
# Measurability of convex-profile direct sums

Source Proposition 4.1.21, for arbitrary measurable profile families in the
uniform topology. No finite-dimensionality or countability of the field is needed.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

/-- The actual completed direct-sum family is measurable for measurable input
families and source-measurable convex profiles. -/
theorem IsMeasurable.directSum {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable) {ψ : S.Ω → NormShape}
    (hψ : NormShape.IsMeasurableFamily ψ) : (ξ.directSum η ψ).IsMeasurable := by
  rintro ⟨x, y⟩
  simpa only [directSum_norm_tmul] using
    hψ.perspective (hξ x) (hη y) (fun ω ↦ ξ.norm_nonneg ω _)
      (fun ω ↦ η.norm_nonneg ω _)

end ArakelovGeometry.NormFamily

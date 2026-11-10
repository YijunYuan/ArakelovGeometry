/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree
public import ArakelovGeometry.AdelicVectorBundle.DeterminantBidual

/-!
# Bidual invariance of Arakelov degree

The canonical bidual adelic bundle uses the established dual and pullback
constructors and the evaluation map on the original vector space. The actual
completed determinant equality proves source equation(4.23), also in rank zero.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual bidual family on the original rational space, with its
measurability supplied by the exact base alternatives. -/
noncomputable def bidualOfMeasurableBase (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    AdelicVectorBundle S E :=
  ((V.dualOfMeasurableBase hS).dualOfMeasurableBase hS).pullback
    (Module.Dual.eval K E) (Module.eval_apply_injective K) (by
      change (V.toNormFamily.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K)).dual.IsMeasurable
      rw [V.toNormFamily.dual_dual_pullback_dual_eq]
      exact V.dual_isMeasurable)

@[simp]
theorem bidualOfMeasurableBase_toNormFamily (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    (V.bidualOfMeasurableBase hS).toNormFamily =
      V.toNormFamily.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K) := rfl

/-- The canonical bidual of any adelic bundle is strongly adelic. -/
theorem bidualOfMeasurableBase_isStronglyAdelic (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.bidualOfMeasurableBase hS).IsStronglyAdelic :=
  ((V.dualOfMeasurableBase hS).dualOfMeasurableBase_isStronglyAdelic hS).pullback
    (Module.Dual.eval K E) (Module.eval_apply_injective K) _ hN

/-- Source equation(4.23), proved by equality of the actual completed
projective determinant norms, with no ultrametricity assumption on the original. -/
theorem degree_bidualOfMeasurableBase [S.IsProper] (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.bidualOfMeasurableBase hS).degree hS hN = V.degree hS hN := by
  let s := (V.determinantOfMeasurableBase hS hN).lineGenerator
    (V.determinantOfMeasurableBase_isLine hS hN)
  rw [(V.bidualOfMeasurableBase hS).degree_eq_neg_integral hS hN s,
    V.degree_eq_neg_integral hS hN s, bidualOfMeasurableBase_toNormFamily,
    V.toNormFamily.determinant_dual_dual_pullback hN]

end ArakelovGeometry.AdelicVectorBundle

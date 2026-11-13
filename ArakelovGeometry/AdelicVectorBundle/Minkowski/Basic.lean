/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Pair

import ArakelovGeometry.AdelicVectorBundle.Minima.InjectiveTensor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Ordinary and strong Minkowski properties on actual bundles

The universal predicates quantify over actual finite-dimensional adelic bundles.
The ordinary property has the actual injective tensor slope comparison as a
consumer. Absolute levels and the same-level strong-to-ordinary implication
are separate mathematical statements.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

universe u v w w'

variable {K : Type u} [Field K]

namespace AdelicStructure

/-- Source Definition 4.3.73, on all actual admissible positive-rank bundles
in the given universe. Zero rank imposes no logarithmic condition. -/
def HasMinkowskiPropertyAtLevel (S : AdelicStructure.{u, v} K) [S.IsProper]
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀
    (V : AdelicVectorBundle.{w} S), 0 < Module.finrank K V →
      V.toNormFamily.IsUltrametricAtFinitePlaces →
      V.maximalSlope - (C * Real.log (Module.finrank K V) : ℝ) ≤
        V.maximalLogarithmicMinimum

/-- Source Definition 4.3.79 with the actual last minimum and minimal slope. -/
def HasStrongMinkowskiPropertyAtLevel (S : AdelicStructure.{u, v} K) [S.IsProper]
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀
    (V : AdelicVectorBundle.{w} S), 0 < Module.finrank K V →
      V.toNormFamily.IsUltrametricAtFinitePlaces →
      V.minimalSlope - (C * Real.log (Module.finrank K V) : ℝ) ≤
        V.minimalLogarithmicMinimum

variable {S : AdelicStructure.{u, v} K} [S.IsProper]
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized] {C D : ℝ}

/-- A larger level weakens the actual universal ordinary inequality. -/
theorem HasMinkowskiPropertyAtLevel.mono (h : S.HasMinkowskiPropertyAtLevel.{u, v, w} C)
    (hCD : C ≤ D) : S.HasMinkowskiPropertyAtLevel.{u, v, w} D := by
  refine ⟨h.1.trans hCD, fun V hr hV => ?_⟩
  have hlog : 0 ≤ Real.log (Module.finrank K V) :=
    Real.log_nonneg (by exact_mod_cast hr)
  exact (EReal.sub_le_sub le_rfl
    (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hCD hlog))).trans
      (h.2 V hr hV)

/-- Strong levels have the same monotonicity with the actual last minimum. -/
theorem HasStrongMinkowskiPropertyAtLevel.mono
    (h : S.HasStrongMinkowskiPropertyAtLevel.{u, v, w} C) (hCD : C ≤ D) :
    S.HasStrongMinkowskiPropertyAtLevel.{u, v, w} D := by
  refine ⟨h.1.trans hCD, fun V hr hV => ?_⟩
  have hlog : 0 ≤ Real.log (Module.finrank K V) :=
    Real.log_nonneg (by exact_mod_cast hr)
  exact (EReal.sub_le_sub le_rfl
    (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hCD hlog))).trans
      (h.2 V hr hV)

/-- The correction is finite, so the ordinary predicate can be rearranged
without assumptions on attainment or finite endpoints. -/
theorem HasMinkowskiPropertyAtLevel.maximalSlope_le
    (h : S.HasMinkowskiPropertyAtLevel.{u, v, w} C)
    (V : AdelicVectorBundle.{w} S) (hr : 0 < Module.finrank K V)
    [hV : V.toNormFamily.IsUltrametricAtFinitePlaces] :
    V.maximalSlope ≤ V.maximalLogarithmicMinimum +
      (C * Real.log (Module.finrank K V) : ℝ) :=
  (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp (h.2 V hr hV)

end AdelicStructure

namespace AdelicVectorBundle

variable {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The first clause of source Corollary 4.3.76 on the actual injective tensor.
The global Minkowski property is applied to this tensor, not assumed of it. -/
theorem maximalSlope_injectiveTensorPair_le_of_minkowski
    (V : AdelicVectorBundle.{w} S) (W : AdelicVectorBundle.{w'} S)
    [hV : V.toNormFamily.IsUltrametricAtFinitePlaces]
      [hW : W.toNormFamily.IsUltrametricAtFinitePlaces]
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    {C : ℝ} (hM : S.HasMinkowskiPropertyAtLevel.{u, v, max w w'} C)
    (hE : 0 < Module.finrank K V) (hF : 0 < Module.finrank K W) :
    (V.injectiveTensorPair W).maximalSlope ≤
      V.maximalSlope + W.maximalSlope +
        (C * Real.log ((Module.finrank K V : ℝ) * Module.finrank K W) : ℝ) := by
  let T := V.injectiveTensorPair W
  have ht : T.toNormFamily.IsUltrametricAtFinitePlaces := inferInstance
  have hr : 0 < Module.finrank K (V ⊗[K] W) := by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos hE hF
  have hl := hM.maximalSlope_le T hr (hV := ht)
  have hu := V.maximalLogarithmicMinimum_injectiveTensorPair_le_maximalSlope_add
    W
  rw [Module.finrank_tensorProduct, Nat.cast_mul] at hl
  exact hl.trans (add_le_add hu le_rfl)

end AdelicVectorBundle
end ArakelovGeometry

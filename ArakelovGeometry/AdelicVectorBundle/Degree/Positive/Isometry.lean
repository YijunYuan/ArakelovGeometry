/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.ExactSequence

import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Positive degree under actual completed isometries

Each rational subspace transports by the existing linear equivalence.
Its actual completed restriction norm, hence its actual degree, is preserved.
The positive-degree supremum is over every subspace; attainment is not used.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u w w' w''

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  {G : Type w''} [AddCommGroup G] [Module K G] [FiniteDimensional K G]

/-- Actual completed isometries transport every subspace degree into the
target positive degree. The zero subspace is included. -/
theorem positiveDegree_le_of_completed_isometry
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S) (e : V ≃ₗ[K] W)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.positiveDegree ≤ W.positiveDegree := by
  apply V.positiveDegree_le
  intro U
  have hu : (V.restrictOfNormMeasurability U).degree =
      (W.restrictOfNormMeasurability (U.map e.toLinearMap)).degree := by
    apply degree_eq_of_completed_isometry _ _ (e.submoduleMap U)
    intro ω z
    exact V.toNormFamily.restrict_map_equiv_norm_eq W.toNormFamily e U ω (he ω) z
  rw [hu]
  exact W.degree_restrict_le_positiveDegree (U.map e.toLinearMap)

/-- Actual completed isometries preserve the positive-degree supremum,
including rank zero, without requiring a maximizing subspace. -/
theorem positiveDegree_eq_of_completed_isometry
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S) (e : V ≃ₗ[K] W)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.positiveDegree = W.positiveDegree := by
  apply le_antisymm (V.positiveDegree_le_of_completed_isometry W e he)
  apply W.positiveDegree_le_of_completed_isometry V e.symm
  intro ω y
  let eω := e.baseChange K (S.ϕ ω).Completion V W
  change V.toNormFamily.norm ω (eω.symm y) = W.toNormFamily.norm ω y
  have h := he ω (eω.symm y)
  change W.toNormFamily.norm ω (eω (eω.symm y)) = V.toNormFamily.norm ω (eω.symm y) at h
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- Pushforward along a genuine surjection has the positive degree of the
actual kernel quotient under the canonical first-isomorphism map. -/
theorem positiveDegree_pushforward_eq_quotient_ker
    (V : AdelicVectorBundle S) (π : V →ₗ[K] F) (hπ : Function.Surjective π)
    [hm : (V.toNormFamily.pushforward π hπ).IsMeasurable]
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.pushforward π hπ).positiveDegree =
      (V.quotientOfNormMeasurability π.ker).positiveDegree := by
  symm
  apply positiveDegree_eq_of_completed_isometry _ _ (π.quotKerEquivOfSurjective hπ)
  intro ω z
  exact V.toNormFamily.quotient_ker_equiv_norm_eq π hπ ω z

/-- The actual left end of any source norm-exact sequence has the positive
degree of the restriction to the middle kernel. -/
theorem positiveDegree_exactSequence_left
    (V : AdelicVectorBundle S) (L : AdelicVectorBundle S) (R : AdelicVectorBundle S)
    (i : L →ₗ[K] V) (p : V →ₗ[K] R)
    (hx : NormFamily.IsExactSequence L.toNormFamily V.toNormFamily R.toNormFamily i p)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    L.positiveDegree = (V.restrictOfNormMeasurability p.ker).positiveDegree := by
  rw [hx.exact.linearMap_ker_eq]
  let e := LinearEquiv.ofInjective i hx.i_injective
  apply positiveDegree_eq_of_completed_isometry _ _ e
  intro ω z
  have hc : i.range.subtype.comp e.toLinearMap = i := by
    ext x
    rfl
  rw [hx.left_norm]
  change V.toNormFamily.norm ω
    (i.range.subtype.baseChange (S.ϕ ω).Completion
      (e.toLinearMap.baseChange (S.ϕ ω).Completion z)) =
    V.toNormFamily.norm ω (i.baseChange (S.ϕ ω).Completion z)
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using
    congrArg (fun f : L →ₗ[K] V ↦ V.toNormFamily.norm ω
      (f.baseChange (S.ϕ ω).Completion z)) hc

/-- The actual right end of a source norm-exact sequence has the positive
degree of the middle kernel quotient, on its original target vector space. -/
theorem positiveDegree_exactSequence_right
    (V : AdelicVectorBundle S) (L : AdelicVectorBundle S) (R : AdelicVectorBundle S)
    (i : L →ₗ[K] V) (p : V →ₗ[K] R)
    (hx : NormFamily.IsExactSequence L.toNormFamily V.toNormFamily R.toNormFamily i p)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    R.positiveDegree = (V.quotientOfNormMeasurability p.ker).positiveDegree := by
  symm
  apply positiveDegree_eq_of_completed_isometry _ _
    (p.quotKerEquivOfSurjective hx.p_surjective)
  intro ω z
  change R.toNormFamily.norm ω
    ((p.quotKerEquivOfSurjective hx.p_surjective).toLinearMap.baseChange
      (S.ϕ ω).Completion z) = (V.toNormFamily.quotient p.ker).norm ω z
  simpa only [hx.right_norm] using
    V.toNormFamily.quotient_ker_equiv_norm_eq p hx.p_surjective ω z

end

end ArakelovGeometry.AdelicVectorBundle

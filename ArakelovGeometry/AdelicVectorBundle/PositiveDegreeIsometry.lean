/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.PositiveDegree
import ArakelovGeometry.AdelicVectorBundle.ExactSequence

/-!
# Positive degree under actual completed isometries

Each rational subspace transports by the existing linear equivalence.
Its actual completed restriction norm, hence its actual degree, is preserved.
The positive-degree supremum is over every subspace; attainment is not used.
-/

namespace ArakelovGeometry.AdelicVectorBundle

noncomputable section

universe u v w w' w''

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  {G : Type w''} [AddCommGroup G] [Module K G] [FiniteDimensional K G]

/-- Actual completed isometries transport every subspace degree into the
target positive degree. The zero subspace is included. -/
theorem positiveDegree_le_of_completed_isometry
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.positiveDegree hS hN ≤ W.positiveDegree hS hN := by
  apply V.positiveDegree_le hS hN
  intro U
  have hu : (V.restrictOfMeasurableBase U hS).degree hS hN =
      (W.restrictOfMeasurableBase (U.map e.toLinearMap) hS).degree hS hN := by
    apply degree_eq_of_completed_isometry _ _ (e.submoduleMap U) hS hN
    intro ω z
    simp only [restrictOfMeasurableBase_toNormFamily]
    exact V.toNormFamily.restrict_map_equiv_norm_eq W.toNormFamily e U ω (he ω) z
  rw [hu]
  exact W.degree_restrict_le_positiveDegree hS hN (U.map e.toLinearMap)

/-- Actual completed isometries preserve the positive-degree supremum,
including rank zero, without requiring a maximizing subspace. -/
theorem positiveDegree_eq_of_completed_isometry
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.positiveDegree hS hN = W.positiveDegree hS hN := by
  apply le_antisymm (V.positiveDegree_le_of_completed_isometry W e hS hN he)
  apply W.positiveDegree_le_of_completed_isometry V e.symm hS hN
  intro ω y
  let eω := e.baseChange K (S.ϕ ω).Completion E F
  change V.toNormFamily.norm ω (eω.symm y) = W.toNormFamily.norm ω y
  have h := he ω (eω.symm y)
  change W.toNormFamily.norm ω (eω (eω.symm y)) = V.toNormFamily.norm ω (eω.symm y) at h
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- Pushforward along a genuine surjection has the positive degree of the
actual kernel quotient under the canonical first-isomorphism map. -/
theorem positiveDegree_pushforward_eq_quotient_ker
    (V : AdelicVectorBundle S E) (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (hm : (V.toNormFamily.pushforward π hπ).IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.pushforward π hπ hm).positiveDegree hS hN =
      (V.quotientOfMeasurableBase π.ker hS).positiveDegree hS hN := by
  symm
  apply positiveDegree_eq_of_completed_isometry _ _ (π.quotKerEquivOfSurjective hπ) hS hN
  intro ω z
  exact V.toNormFamily.quotient_ker_equiv_norm_eq π hπ ω z

/-- The actual left end of any source norm-exact sequence has the positive
degree of the restriction to the middle kernel. -/
theorem positiveDegree_exactSequence_left
    (V : AdelicVectorBundle S E) (L : AdelicVectorBundle S F) (R : AdelicVectorBundle S G)
    (i : F →ₗ[K] E) (p : E →ₗ[K] G)
    (hx : NormFamily.IsExactSequence L.toNormFamily V.toNormFamily R.toNormFamily i p)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    L.positiveDegree hS hN = (V.restrictOfMeasurableBase p.ker hS).positiveDegree hS hN := by
  rw [hx.exact.linearMap_ker_eq]
  let e := LinearEquiv.ofInjective i hx.i_injective
  apply positiveDegree_eq_of_completed_isometry _ _ e hS hN
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
    congrArg (fun f : F →ₗ[K] E ↦ V.toNormFamily.norm ω
      (f.baseChange (S.ϕ ω).Completion z)) hc

/-- The actual right end of a source norm-exact sequence has the positive
degree of the middle kernel quotient, on its original target vector space. -/
theorem positiveDegree_exactSequence_right
    (V : AdelicVectorBundle S E) (L : AdelicVectorBundle S F) (R : AdelicVectorBundle S G)
    (i : F →ₗ[K] E) (p : E →ₗ[K] G)
    (hx : NormFamily.IsExactSequence L.toNormFamily V.toNormFamily R.toNormFamily i p)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    R.positiveDegree hS hN = (V.quotientOfMeasurableBase p.ker hS).positiveDegree hS hN := by
  symm
  apply positiveDegree_eq_of_completed_isometry _ _
    (p.quotKerEquivOfSurjective hx.p_surjective) hS hN
  intro ω z
  change R.toNormFamily.norm ω
    ((p.quotKerEquivOfSurjective hx.p_surjective).toLinearMap.baseChange
      (S.ϕ ω).Completion z) = (V.toNormFamily.quotient p.ker).norm ω z
  simpa only [hx.right_norm] using
    V.toNormFamily.quotient_ker_equiv_norm_eq p hx.p_surjective ω z

end

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Basic

import ArakelovGeometry.AdelicVectorBundle.Determinant.Functor
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Elementary
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Majorant discrepancy under actual completed isometries

Actual elementary majorants transport by injective pullback along a rational
linear equivalence. The determinant ratios and their infimum are therefore
preserved, as is the global lower-envelope integral. Canonical nested and
total restrictions are included without rank restrictions.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- Every actual elementary majorant on the target pulls back to one on the
source with the same actual determinant ratio. -/
theorem majorantRatios_subset_of_completed_isometry (ξ : NormFamily S E)
    (η : NormFamily S F) (e : E ≃ₗ[K] F)
    [hN : S.IsArchimedeanNormalized] (ω : S.Ω)
    (he : ∀ x, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x) :
    η.majorantRatios ω ⊆ ξ.majorantRatios ω := by
  rintro a ⟨α, ha, hle, rfl⟩
  let β := α.pullback e.toLinearMap e.injective
  let z := (1 : (S.ϕ ω).Completion) ⊗ₜ[K] determinantGenerator (K := K) (E := E)
  let D := (determinantEquiv K e).baseChange K (S.ϕ ω).Completion _ _
  have hz : z ≠ 0 := by
    intro h
    have hp := ξ.determinant.norm_rational_pos ω
      (determinantGenerator_ne_zero (K := K) (E := E))
    change 0 < ξ.determinant.norm ω z at hp
    rw [h, ξ.determinant.norm_zero] at hp
    exact (lt_irrefl 0) hp
  have hDz : D z ≠ 0 := by
    intro h
    exact hz (D.injective (h.trans D.map_zero.symm))
  have hβ := β.determinantEquiv_norm_eq α ω e (fun _ ↦ rfl) z
  have hξ := ξ.determinantEquiv_norm_eq η ω e he z
  have hratio := η.determinantRatio_eq_of_nonzero α ω (D z) hDz
  refine ⟨β, ha.pullback e.toLinearMap e.injective, ?_, ?_⟩
  · intro x
    change ξ.norm ω x ≤ α.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x)
    rw [← he]
    exact hle _
  · rw [← hratio, hβ, hξ]

/-- Completed-fibre isometries identify the full actual elementary-majorant
candidate sets; the generators on the two determinant lines need not agree. -/
theorem majorantRatios_eq_of_completed_isometry (ξ : NormFamily S E)
    (η : NormFamily S F) (e : E ≃ₗ[K] F)
    [hN : S.IsArchimedeanNormalized] (ω : S.Ω)
    (he : ∀ x, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x) :
    ξ.majorantRatios ω = η.majorantRatios ω := by
  apply Set.Subset.antisymm _ (ξ.majorantRatios_subset_of_completed_isometry η e ω he)
  apply η.majorantRatios_subset_of_completed_isometry ξ e.symm ω
  intro y
  let eω := e.baseChange K (S.ϕ ω).Completion E F
  change ξ.norm ω (eω.symm y) = η.norm ω y
  have h := he (eω.symm y)
  change η.norm ω (eω (eω.symm y)) = ξ.norm ω (eω.symm y) at h
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- The actual local infimum, including its rank-zero convention, is invariant
under every rational completed-fibre isometry. -/
theorem majorantDiscrepancy_eq_of_completed_isometry (ξ : NormFamily S E)
    (η : NormFamily S F) (e : E ≃ₗ[K] F)
    [hN : S.IsArchimedeanNormalized] (ω : S.Ω)
    (he : ∀ x, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x) :
    ξ.majorantDiscrepancy ω = η.majorantDiscrepancy ω := by
  rw [majorantDiscrepancy, majorantDiscrepancy, e.finrank_eq,
    ξ.majorantRatios_eq_of_completed_isometry η e ω he]

/-- The local majorant infimum of a nested actual restriction equals that
of the direct restriction, in every rank and at every place. -/
theorem majorantDiscrepancy_restrict_restrict (ξ : NormFamily S E)
    (U W : Submodule K E) (h : U ≤ W)
    [hN : S.IsArchimedeanNormalized] (ω : S.Ω) :
    ((ξ.restrict W).restrict (U.comap W.subtype)).majorantDiscrepancy ω =
      (ξ.restrict U).majorantDiscrepancy ω := by
  apply majorantDiscrepancy_eq_of_completed_isometry _ _
    (Submodule.comapSubtypeEquivOfLe h) ω
  intro z
  exact (ξ.restrict_restrict_norm_eq U W h ω z).symm

/-- Total restriction preserves the actual local elementary-majorant infimum. -/
theorem majorantDiscrepancy_restrict_top (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized] (ω : S.Ω) :
    (ξ.restrict ⊤).majorantDiscrepancy ω = ξ.majorantDiscrepancy ω := by
  apply majorantDiscrepancy_eq_of_completed_isometry _ _ Submodule.topEquiv ω
  intro z
  exact (ξ.restrict_top_norm_eq ω z).symm

end NormFamily

namespace AdelicVectorBundle

/-- The actual lower-envelope integral of the local majorant infimum is
preserved by completed-fibre isometries, even when it equals positive infinity. -/
theorem majorantDiscrepancy_eq_of_completed_isometry
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S) (e : V ≃ₗ[K] W)
    [hN : S.IsArchimedeanNormalized]
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.majorantDiscrepancy = W.majorantDiscrepancy := by
  unfold majorantDiscrepancy
  congr 1
  funext ω
  rw [V.toNormFamily.majorantDiscrepancy_eq_of_completed_isometry
    W.toNormFamily e ω (he ω)]

/-- Canonical nested restriction preserves the global capital discrepancy
of the actual norm family. -/
theorem majorantDiscrepancy_restrict_restrict (V : AdelicVectorBundle S)
    (U W : Submodule K V) (h : U ≤ W)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    ((V.restrictOfNormMeasurability W).restrictOfNormMeasurability
      (U.comap W.subtype)).majorantDiscrepancy =
      (V.restrictOfNormMeasurability U).majorantDiscrepancy := by
  apply majorantDiscrepancy_eq_of_completed_isometry _ _
    (Submodule.comapSubtypeEquivOfLe h)
  intro ω z
  exact (V.toNormFamily.restrict_restrict_norm_eq U W h ω z).symm

/-- Restriction to the total subspace preserves the actual global capital
discrepancy, without a finiteness assumption on its lower integral. -/
theorem majorantDiscrepancy_restrict_top (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized] :
    (V.restrictOfNormMeasurability ⊤).majorantDiscrepancy =
      V.majorantDiscrepancy := by
  apply majorantDiscrepancy_eq_of_completed_isometry _ _ Submodule.topEquiv
  intro ω z
  exact (V.toNormFamily.restrict_top_norm_eq ω z).symm

end AdelicVectorBundle

end

end ArakelovGeometry

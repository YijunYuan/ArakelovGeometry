/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Discrepancy
public import ArakelovGeometry.AdelicVectorBundle.ElementaryRestrictionQuotient
public import ArakelovGeometry.AdelicVectorBundle.RestrictionFunctor

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

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- Every actual elementary majorant on the target pulls back to one on the
source with the same actual determinant ratio. -/
theorem majorantRatios_subset_of_completed_isometry (ξ : NormFamily S E)
    (η : NormFamily S F) (e : E ≃ₗ[K] F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω)
    (he : ∀ x, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x) :
    η.majorantRatios hN ω ⊆ ξ.majorantRatios hN ω := by
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
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω)
    (he : ∀ x, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x) :
    ξ.majorantRatios hN ω = η.majorantRatios hN ω := by
  apply Set.Subset.antisymm _ (ξ.majorantRatios_subset_of_completed_isometry η e hN ω he)
  apply η.majorantRatios_subset_of_completed_isometry ξ e.symm hN ω
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
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω)
    (he : ∀ x, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x) :
    ξ.majorantDiscrepancy hN ω = η.majorantDiscrepancy hN ω := by
  rw [majorantDiscrepancy, majorantDiscrepancy, e.finrank_eq,
    ξ.majorantRatios_eq_of_completed_isometry η e hN ω he]

/-- The local majorant infimum of a nested actual restriction equals that
of the direct restriction, in every rank and at every place. -/
theorem majorantDiscrepancy_restrict_restrict (ξ : NormFamily S E)
    (U W : Submodule K E) (h : U ≤ W)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) :
    ((ξ.restrict W).restrict (U.comap W.subtype)).majorantDiscrepancy hN ω =
      (ξ.restrict U).majorantDiscrepancy hN ω := by
  apply majorantDiscrepancy_eq_of_completed_isometry _ _
    (Submodule.comapSubtypeEquivOfLe h) hN ω
  intro z
  exact (ξ.restrict_restrict_norm_eq U W h ω z).symm

/-- Total restriction preserves the actual local elementary-majorant infimum. -/
theorem majorantDiscrepancy_restrict_top (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) :
    (ξ.restrict ⊤).majorantDiscrepancy hN ω = ξ.majorantDiscrepancy hN ω := by
  apply majorantDiscrepancy_eq_of_completed_isometry _ _ Submodule.topEquiv hN ω
  intro z
  exact (ξ.restrict_top_norm_eq ω z).symm

end NormFamily

namespace AdelicVectorBundle

/-- The actual lower-envelope integral of the local majorant infimum is
preserved by completed-fibre isometries, even when it equals positive infinity. -/
theorem majorantDiscrepancy_eq_of_completed_isometry
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.majorantDiscrepancy hN = W.majorantDiscrepancy hN := by
  unfold majorantDiscrepancy
  congr 1
  funext ω
  rw [V.toNormFamily.majorantDiscrepancy_eq_of_completed_isometry
    W.toNormFamily e hN ω (he ω)]

/-- Canonical nested restriction preserves the global capital discrepancy
of the actual norm family. -/
theorem majorantDiscrepancy_restrict_restrict (V : AdelicVectorBundle S E)
    (U W : Submodule K E) (h : U ≤ W)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.restrictOfMeasurableBase W hS).restrictOfMeasurableBase
      (U.comap W.subtype) hS).majorantDiscrepancy hN =
      (V.restrictOfMeasurableBase U hS).majorantDiscrepancy hN := by
  apply majorantDiscrepancy_eq_of_completed_isometry _ _
    (Submodule.comapSubtypeEquivOfLe h) hN
  intro ω z
  simp only [restrictOfMeasurableBase_toNormFamily]
  exact (V.toNormFamily.restrict_restrict_norm_eq U W h ω z).symm

/-- Restriction to the total subspace preserves the actual global capital
discrepancy, without a finiteness assumption on its lower integral. -/
theorem majorantDiscrepancy_restrict_top (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.restrictOfMeasurableBase ⊤ hS).majorantDiscrepancy hN =
      V.majorantDiscrepancy hN := by
  apply majorantDiscrepancy_eq_of_completed_isometry _ _ Submodule.topEquiv hN
  intro ω z
  simp only [restrictOfMeasurableBase_toNormFamily]
  exact (V.toNormFamily.restrict_top_norm_eq ω z).symm

end AdelicVectorBundle

end

end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.DegreeIsometry
import ArakelovGeometry.AdelicVectorBundle.Discrepancy
import ArakelovGeometry.AdelicVectorBundle.DualMap
import ArakelovGeometry.AdelicVectorBundle.RestrictionFunctor

/-!
# Dual degree and discrepancy preserved by completed isometries

The transpose of a rational completed-fibre isometry preserves the actual
completed dual norms. This identifies dual degrees and hence the actual
global determinant discrepancy, also in rank zero and at trivial valuations.
-/

open scoped TensorProduct

namespace ArakelovGeometry

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- The actual completed transpose preserves the actual dual norm when the
original rational equivalence preserves every completed vector norm. -/
theorem dualEquiv_norm_eq_of_completed_isometry (ξ : NormFamily S E)
    (η : NormFamily S F) (ω : S.Ω) (e : E ≃ₗ[K] F)
    (he : ∀ x, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K F) :
    ξ.dual.norm ω (e.dualMap.toLinearMap.baseChange (S.ϕ ω).Completion z) =
      η.dual.norm ω z := by
  change ξ.dual.norm ω (e.toLinearMap.dualMap.baseChange (S.ϕ ω).Completion z) =
    η.dual.norm ω z
  apply le_antisymm
  · apply ξ.dual_norm_le ω _ (η.dual.norm_nonneg ω z)
    intro x
    rw [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply]
    simpa only [he] using η.norm_dual_apply_le ω z
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x)
  · apply η.dual_norm_le ω z (ξ.dual.norm_nonneg ω _)
    intro y
    obtain ⟨x, rfl⟩ := (e.baseChange K (S.ϕ ω).Completion E F).surjective y
    change ‖dualBaseChangeEquiv K (S.ϕ ω).Completion F z
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x)‖ ≤
        ξ.dual.norm ω (e.toLinearMap.dualMap.baseChange (S.ϕ ω).Completion z) *
          η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x)
    simpa only [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply, he] using
      ξ.norm_dual_apply_le ω (e.toLinearMap.dualMap.baseChange
        (S.ϕ ω).Completion z) x

end NormFamily

namespace AdelicVectorBundle

/-- Dual degrees agree under the actual contravariant completed isometry. -/
theorem degree_dual_eq_of_completed_isometry [S.IsProper]
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    (V.dualOfMeasurableBase hS).degree hS hN =
      (W.dualOfMeasurableBase hS).degree hS hN := by
  symm
  apply degree_eq_of_completed_isometry _ _ e.dualMap hS hN
  intro ω z
  simp only [dualOfMeasurableBase_toNormFamily]
  exact V.toNormFamily.dualEquiv_norm_eq_of_completed_isometry W.toNormFamily ω e (he ω) z

/-- Actual completed-fibre isometries preserve the global real determinant
discrepancy, without any original finite-place ultrametricity assumption. -/
theorem determinantDiscrepancy_eq_of_completed_isometry [S.IsProper]
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.toNormFamily.norm ω x) :
    V.determinantDiscrepancy = W.determinantDiscrepancy := by
  rw [V.determinantDiscrepancy_eq_degree_add_degree_dual hS hN,
    W.determinantDiscrepancy_eq_degree_add_degree_dual hS hN,
    V.degree_eq_of_completed_isometry W e hS hN he,
    V.degree_dual_eq_of_completed_isometry W e hS hN he]

/-- Nested restriction preserves the actual global discrepancy under the
existing canonical rational subspace isomorphism. -/
theorem determinantDiscrepancy_restrict_restrict [S.IsProper]
    (V : AdelicVectorBundle S E) (U W : Submodule K E) (h : U ≤ W)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.restrictOfMeasurableBase W hS).restrictOfMeasurableBase
      (U.comap W.subtype) hS).determinantDiscrepancy =
      (V.restrictOfMeasurableBase U hS).determinantDiscrepancy := by
  apply determinantDiscrepancy_eq_of_completed_isometry _ _
    (Submodule.comapSubtypeEquivOfLe h) hS hN
  intro ω z
  simp only [restrictOfMeasurableBase_toNormFamily]
  exact (V.toNormFamily.restrict_restrict_norm_eq U W h ω z).symm

/-- The total rational subspace has the actual ambient global discrepancy. -/
theorem determinantDiscrepancy_restrict_top [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.restrictOfMeasurableBase ⊤ hS).determinantDiscrepancy =
      V.determinantDiscrepancy := by
  apply determinantDiscrepancy_eq_of_completed_isometry _ _ Submodule.topEquiv hS hN
  intro ω z
  simp only [restrictOfMeasurableBase_toNormFamily]
  exact (V.toNormFamily.restrict_top_norm_eq ω z).symm

end AdelicVectorBundle

end ArakelovGeometry

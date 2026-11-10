/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminant
public import ArakelovGeometry.AdelicVectorBundle.DeterminantFunctor

/-!
# Actual measurable determinants under completed isometries

A rational linear equivalence preserving all completed norms transports actual
determinant measurability and determinant degree without place-space regularity.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v w w'
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- A rational equivalence preserving every completed norm transports actual
rational norm measurability, without regularity of the place space. -/
theorem IsMeasurable.of_completed_isometry (ξ : NormFamily S E) (η : NormFamily S F)
    (e : E ≃ₗ[K] F)
    (he : ∀ ω z, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion z) = ξ.norm ω z)
    (hξ : ξ.IsMeasurable) : η.IsMeasurable := by
  intro y
  have hn (ω : S.Ω) :
      η.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] y) =
        ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] e.symm y) := by
    simpa only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      e.apply_symm_apply] using he ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] e.symm y)
  change Measurable (fun ω : S.Ω => η.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] y))
  have hf := funext hn
  rw [hf]
  exact hξ (e.symm y)

/-- An actual completed isometry produces target determinant measurability
from the source's actual determinant measurability, including rank zero. -/
theorem determinant_isMeasurable_of_completed_isometry
    (ξ : NormFamily S E) (η : NormFamily S F) (e : E ≃ₗ[K] F)
    (he : ∀ ω z, η.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion z) = ξ.norm ω z)
    (hdet : ξ.determinant.IsMeasurable) : η.determinant.IsMeasurable := by
  apply IsMeasurable.of_completed_isometry ξ.determinant η.determinant
    (determinantEquiv K e) _ hdet
  intro ω z
  exact ξ.determinantEquiv_norm_eq η ω e (he ω) z

end NormFamily

namespace AdelicVectorBundle

/-- Degree of the actual measurable determinant is preserved by an actual
completed isometry. Target determinant measurability is produced, not assumed. -/
theorem degreeOfMeasurableDeterminant_eq_of_completed_isometry [S.IsProper]
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hdet : V.toNormFamily.determinant.IsMeasurable)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω z, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion z) = V.toNormFamily.norm ω z) :
    V.degreeOfMeasurableDeterminant hdet hN =
      W.degreeOfMeasurableDeterminant
        (V.toNormFamily.determinant_isMeasurable_of_completed_isometry
          W.toNormFamily e he hdet) hN := by
  let hW := V.toNormFamily.determinant_isMeasurable_of_completed_isometry
    W.toNormFamily e he hdet
  apply lineDegree_eq_of_norm_rational_eq
    (V.determinant hdet hN) (W.determinant hW hN)
    (V.determinant_isLine hdet hN) (W.determinant_isLine hW hN) (determinantEquiv K e)
  intro ω z
  have h := V.toNormFamily.determinantEquiv_norm_eq W.toNormFamily ω e (he ω)
    ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z)
  have h' : W.toNormFamily.determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] determinantEquiv K e z) =
      V.toNormFamily.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z) := by
    simpa only [LinearEquiv.baseChange_tmul] using h
  exact h'.symm

end AdelicVectorBundle
end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Archimedean.TraceDualNorm
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import Mathlib.Topology.Sheaves.Init

/-! # Trace duality for the ordinary Euclidean product metric

The primal norm squared is the unweighted sum of the prescribed fibre norm
squares. The dual norm squared is the unweighted sum of `(w.mult * p_w*)²`.
Both metrics are defined independently of the trace map on the same actual
completed vector products. In particular a complex dual fibre has factor two.
-/

@[expose] public section

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldOrdinaryTraceDualNorm

open AdelicStructure NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldArchimedeanTracePairing NumberFieldArchimedeanTraceDualNorm

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

omit [FiniteDimensional K E] in
/-- Coordinate multiplication by the actual local degree, on the original product. -/
def multiplicityEquiv : CompletedVectorProduct K E ≃ₗ[ℝ] CompletedVectorProduct K E :=
  LinearEquiv.piCongrRight (fun w =>
    LinearEquiv.smulOfNeZero ℝ (CompletedCoefficient w ⊗[K] E)
      (w.mult : ℝ) (by exact_mod_cast (InfinitePlace.mult_pos (w := w)).ne'))

omit [FiniteDimensional K E] in
@[simp]
theorem multiplicityEquiv_apply (z : CompletedVectorProduct K E) (w : InfinitePlace K) :
    multiplicityEquiv (K := K) (E := E) z w = (w.mult : ℝ) • z w := rfl

/-- The ordinary trace-dual metric, independently defined by degree scaling of the
original Euclidean product of the actual dual norms. -/
abbrev ordinaryTraceDualNormedAddCommGroup
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    NormedAddCommGroup (CompletedVectorProduct K (Module.Dual K E)) := by
  let := euclideanNormedAddCommGroup ξ.dual
  exact NormedAddCommGroup.induced _ _ multiplicityEquiv.toLinearMap
    multiplicityEquiv.injective

/-- The prescribed real scalar action with the independently defined ordinary dual norm. -/
abbrev ordinaryTraceDualNormedSpace
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    letI := ordinaryTraceDualNormedAddCommGroup ξ
    NormedSpace ℝ (CompletedVectorProduct K (Module.Dual K E)) := by
  let := euclideanNormedAddCommGroup ξ.dual
  let := euclideanNormedSpace ξ.dual
  exact NormedSpace.induced ℝ _ _ multiplicityEquiv.toLinearMap

theorem ordinaryTraceDual_norm_sq
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    letI := ordinaryTraceDualNormedAddCommGroup ξ
    ‖f‖ ^ 2 = ∑ w : InfinitePlace K,
      ((w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) (f w)) ^ 2 := by
  let : ∀ w : InfinitePlace K,
      NormedAddCommGroup (CompletedCoefficient w ⊗[K] Module.Dual K E) :=
    fun w => ξ.dual.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let : ∀ w : InfinitePlace K,
      NormedSpace ℝ (CompletedCoefficient w ⊗[K] Module.Dual K E) :=
    fun w => fibreRealNormedSpace ξ.dual w
  let := euclideanNormedAddCommGroup ξ.dual
  change ‖multiplicityEquiv (K := K) (E := Module.Dual K E) f‖ ^ 2 = _
  rw [euclidean_norm_sq]
  apply Finset.sum_congr rfl
  intro w _
  change ‖(w.mult : ℝ) • f w‖ ^ 2 = ((w.mult : ℝ) * ‖f w‖) ^ 2
  rw [_root_.norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]

omit [FiniteDimensional K E] in
/-- The ordinary primal product inner product is the unweighted sum of fibre products. -/
theorem ordinaryInner_eq_sum
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (z x : CompletedVectorProduct K E) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanInnerProduct hξ
    inner ℝ z x = ∑ w : InfinitePlace K, localInner hξ w (z w) (x w) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  simp only [← pow_two, euclidean_norm_sq, localInner_polarization, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]

/-- The local trace Riesz representatives in the ordinary, unweighted primal product. -/
def ordinaryTraceRiesz
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) : CompletedVectorProduct K E :=
  fun w => localTraceRiesz hξ w (f w)

theorem ordinaryTraceRiesz_inner
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) (x : CompletedVectorProduct K E) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanInnerProduct hξ
    inner ℝ (ordinaryTraceRiesz hξ f) x = tracePairing (K := K) (E := E) f x := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  rw [ordinaryInner_eq_sum, tracePairing_apply]
  apply Finset.sum_congr rfl
  intro w _
  exact localTraceRiesz_inner hξ w (f w) (x w)

theorem ordinaryTraceRiesz_norm_sq
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    letI := euclideanNormedAddCommGroup ξ
    ‖ordinaryTraceRiesz hξ f‖ ^ 2 = ∑ w : InfinitePlace K,
      ((w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) (f w)) ^ 2 := by
  let := euclideanNormedAddCommGroup ξ
  rw [euclidean_norm_sq]
  simp only [ordinaryTraceRiesz, norm_localTraceRiesz]

/-- The literal trace pairing as a functional on the ordinary primal Euclidean metric. -/
def ordinaryTracePairingCLM
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    StrongDual ℝ (CompletedVectorProduct K E) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  exact LinearMap.toContinuousLinearMap (tracePairing (K := K) (E := E) f)

@[simp]
theorem ordinaryTracePairingCLM_apply
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (f : CompletedVectorProduct K (Module.Dual K E)) (x : CompletedVectorProduct K E) :
    ordinaryTracePairingCLM ξ f x = tracePairing (K := K) (E := E) f x := rfl

theorem ordinaryTracePairingCLM_norm_sq
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    ‖ordinaryTracePairingCLM ξ f‖ ^ 2 = ∑ w : InfinitePlace K,
      ((w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) (f w)) ^ 2 := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  have he : ordinaryTracePairingCLM ξ f =
      InnerProductSpace.toDual ℝ _ (ordinaryTraceRiesz hξ f) := by
    ext x
    exact (ordinaryTraceRiesz_inner hξ f x).symm
  rw [he, LinearIsometryEquiv.norm_map]
  exact ordinaryTraceRiesz_norm_sq hξ f

theorem ordinaryTracePairingCLM_norm
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := ordinaryTraceDualNormedAddCommGroup ξ
    ‖ordinaryTracePairingCLM ξ f‖ = ‖f‖ := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := ordinaryTraceDualNormedAddCommGroup ξ
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ordinaryTracePairingCLM_norm_sq hξ, ordinaryTraceDual_norm_sq]

/-- The original trace pairing, isometrically to the ordinary real continuous dual.
The domain metric has local factors `w.mult`, including factor two at complex places. -/
def ordinaryTraceDualIsometry
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := ordinaryTraceDualNormedAddCommGroup ξ
    letI := ordinaryTraceDualNormedSpace ξ
    CompletedVectorProduct K (Module.Dual K E) ≃ₗᵢ[ℝ]
      StrongDual ℝ (CompletedVectorProduct K E) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := ordinaryTraceDualNormedAddCommGroup ξ
  let := ordinaryTraceDualNormedSpace ξ
  exact { (tracePairingEquiv (K := K) (E := E)).trans LinearMap.toContinuousLinearMap with
    norm_map' := ordinaryTracePairingCLM_norm hξ }

@[simp]
theorem ordinaryTraceDualIsometry_apply
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) (x : CompletedVectorProduct K E) :
    ordinaryTraceDualIsometry hξ f x = tracePairing (K := K) (E := E) f x := rfl

theorem ordinaryTraceDualIsometry_original
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : Module.Dual K E) (x : E) :
    ordinaryTraceDualIsometry hξ (vectorDiagonalMap (K := K) f)
      (vectorDiagonalMap (K := K) x) = (Algebra.trace ℚ K (f x) : ℝ) := by
  rw [ordinaryTraceDualIsometry_apply, tracePairing_original]

theorem ordinaryTraceDualIsometry_integral
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (M : Submodule (𝓞 K) E) (f : NumberFieldIntegralTraceDual.integralTraceDual M) (m : M) :
    ordinaryTraceDualIsometry hξ (vectorDiagonalMap (K := K) (f : Module.Dual K E))
      (vectorDiagonalMap (K := K) (m : E)) ∈ LinearMap.range (Algebra.linearMap ℤ ℝ) := by
  refine ⟨NumberFieldIntegralTraceDual.traceRestriction M f m, ?_⟩
  change (NumberFieldIntegralTraceDual.traceRestriction M f m : ℝ) = _
  rw [ordinaryTraceDualIsometry_original]
  exact_mod_cast NumberFieldIntegralTraceDual.traceRestriction_apply M f m

/-- The actual integral trace-dual diagonal has precisely the original integer-valued
real dual image under the ordinary trace isometry, through the canonical continuous dual. -/
theorem ordinaryTraceDualIsometry_integral_image
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := ordinaryTraceDualNormedAddCommGroup ξ
    letI := ordinaryTraceDualNormedSpace ξ
    (diagonalLattice (NumberFieldIntegralTraceDual.integralTraceDual M)).map
      ((ordinaryTraceDualIsometry hξ).toLinearEquiv.toLinearMap.restrictScalars ℤ) =
        (integralRealDual M).map
          ((LinearMap.toContinuousLinearMap :
            Module.Dual ℝ (CompletedVectorProduct K E) ≃ₗ[ℝ]
              StrongDual ℝ (CompletedVectorProduct K E)).toLinearMap.restrictScalars ℤ) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := ordinaryTraceDualNormedAddCommGroup ξ
  let := ordinaryTraceDualNormedSpace ξ
  have he : (ordinaryTraceDualIsometry hξ).toLinearEquiv.toLinearMap.restrictScalars ℤ =
      ((LinearMap.toContinuousLinearMap :
        Module.Dual ℝ (CompletedVectorProduct K E) ≃ₗ[ℝ]
          StrongDual ℝ (CompletedVectorProduct K E)).toLinearMap.restrictScalars ℤ).comp
            ((tracePairing (K := K) (E := E)).restrictScalars ℤ) := rfl
  rw [he, Submodule.map_comp, tracePairing_diagonal_integralTraceDual_image M hfg hspan]

end ArakelovGeometry.NumberFieldOrdinaryTraceDualNorm

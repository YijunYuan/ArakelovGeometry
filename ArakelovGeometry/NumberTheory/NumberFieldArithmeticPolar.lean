/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberFieldArithmeticProductBall
public import ArakelovGeometry.NumberTheory.NumberFieldProjectiveTraceDualMetric
public import Mathlib.Analysis.LocallyConvex.Polar

/-! # The actual arithmetic product-ball polar set and its prescribed tensor containment -/

@[expose] public section

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldArithmeticPolar

open AdelicStructure NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldArchimedeanTracePairing NumberFieldArchimedeanTraceDualNorm
  NumberFieldOrdinaryTraceDualNorm NumberFieldArithmeticProductBall
  NumberFieldProjectiveTraceDualMetric
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

universe u
variable {K E : Type u} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

private theorem unit_inner_maximizer {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (r : V) :
    ∃ x : V, ‖x‖ ≤ 1 ∧ inner ℝ r x = ‖r‖ := by
  by_cases hr : r = 0
  · subst r
    exact ⟨0, by simp, by simp⟩
  · have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
    refine ⟨‖r‖⁻¹ • r, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    · rw [inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp

/-- An actual completed unit vector attains each local real trace functional norm,
including zero-dimensional fibres. -/
theorem exists_local_trace_maximizer
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (w : InfinitePlace K) (f : CompletedCoefficient w ⊗[K] Module.Dual K E) :
    ∃ x : CompletedCoefficient w ⊗[K] E,
      ξ.norm (normalizedInfinitePlacePoint w) x ≤ 1 ∧
      localTraceDualMap (K := K) (E := E) w f x =
        (w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) f := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  let := localRealInnerProduct hξ w
  obtain ⟨x, hx, he⟩ := unit_inner_maximizer (localTraceRiesz hξ w f)
  refine ⟨x, hx, ?_⟩
  rw [localTraceRiesz_inner] at he
  exact he.trans (norm_localTraceRiesz hξ w f)

/-- The actual trace pairing attains the sum of its actual local trace-dual norms
on the original product of completed unit balls. -/
theorem exists_product_trace_maximizer
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    ∃ x ∈ productBall ξ 1, tracePairing (K := K) (E := E) f x =
      ∑ w : InfinitePlace K,
        (w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) (f w) := by
  choose x hx he using fun w => exists_local_trace_maximizer hξ w (f w)
  refine ⟨x, hx, ?_⟩
  change (∑ w, localTraceDualMap (K := K) (E := E) w (f w) (x w)) = _
  exact Finset.sum_congr rfl (fun w _ => he w)

/-- The actual trace pairing on the original product ball is bounded by the sum
of the independently prescribed local trace-dual norms. -/
theorem tracePairing_bound_productBall
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (f : CompletedVectorProduct K (Module.Dual K E))
    {x : CompletedVectorProduct K E} (hx : x ∈ productBall ξ 1) :
    ‖tracePairing (K := K) (E := E) f x‖ ≤
      ∑ w : InfinitePlace K,
        (w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) (f w) := by
  change ‖∑ w, localTraceDualMap (K := K) (E := E) w (f w) (x w)‖ ≤ _
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  exact (localTraceDualMap_bound ξ w (f w) (x w)).trans
    ((mul_le_mul_of_nonneg_left (hx w)
      (mul_nonneg (Nat.cast_nonneg _) (ξ.dual.norm_nonneg _ _))).trans_eq (mul_one _))

/-- The native actual real continuous-dual polar is the sum of the actual local
trace-dual norms, through the existing ordinary trace isometry. -/
theorem ordinaryTraceDualIsometry_mem_polar
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := ordinaryTraceDualNormedAddCommGroup ξ
    letI := ordinaryTraceDualNormedSpace ξ
    ordinaryTraceDualIsometry hξ f ∈ StrongDual.polar ℝ (productBall ξ 1) ↔
      (∑ w : InfinitePlace K,
        (w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) (f w)) ≤ 1 := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := ordinaryTraceDualNormedAddCommGroup ξ
  let := ordinaryTraceDualNormedSpace ξ
  constructor
  · intro hf
    obtain ⟨x, hx, he⟩ := exists_product_trace_maximizer hξ f
    have h := hf x hx
    change ‖tracePairing (K := K) (E := E) f x‖ ≤ 1 at h
    rw [he, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun w _ =>
        mul_nonneg (Nat.cast_nonneg _) (ξ.dual.norm_nonneg _ _))] at h
    exact h
  · intro hf x hx
    change ‖tracePairing (K := K) (E := E) f x‖ ≤ 1
    exact (tracePairing_bound_productBall ξ f hx).trans hf

/-- The actual prescribed dual tensor followed by ordinary real trace duality,
with the original completed tensor-unit map and all existing norm structures. -/
def arithmeticTraceTensorIsometry
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanNormedAddCommGroup (prescribedTraceDualFamily hξ)
    letI := euclideanNormedSpace (prescribedTraceDualFamily hξ)
    CompletedVectorProduct K (Module.Dual K E ⊗[K] K) ≃ₗᵢ[ℝ]
      StrongDual ℝ (CompletedVectorProduct K E) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanNormedAddCommGroup (prescribedTraceDualFamily hξ)
  let := euclideanNormedSpace (prescribedTraceDualFamily hξ)
  let := ordinaryTraceDualNormedAddCommGroup ξ
  let := ordinaryTraceDualNormedSpace ξ
  exact (prescribedTraceDualIsometry hξ).trans (ordinaryTraceDualIsometry hξ)

/-- Exact polar set in the actual prescribed dual-tensor completed product.
The actual component norms already include the real1/complex2 trace factors. -/
theorem prescribedTraceDual_polar
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanNormedAddCommGroup (prescribedTraceDualFamily hξ)
    letI := euclideanNormedSpace (prescribedTraceDualFamily hξ)
    arithmeticTraceTensorIsometry hξ ⁻¹' StrongDual.polar ℝ (productBall ξ 1) =
      {z | (∑ w : InfinitePlace K,
        (prescribedTraceDualFamily hξ).norm (normalizedInfinitePlacePoint w) (z w)) ≤ 1} := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanNormedAddCommGroup (prescribedTraceDualFamily hξ)
  let := euclideanNormedSpace (prescribedTraceDualFamily hξ)
  let := ordinaryTraceDualNormedAddCommGroup ξ
  let := ordinaryTraceDualNormedSpace ξ
  ext z
  have h := ordinaryTraceDualIsometry_mem_polar hξ
    (tensorUnitProductEquiv (K := K) (E := Module.Dual K E) z)
  have hs : (∑ w : InfinitePlace K, (w.mult : ℝ) *
      ξ.dual.norm (normalizedInfinitePlacePoint w)
        (tensorUnitProductEquiv (K := K) (E := Module.Dual K E) z w)) =
      ∑ w : InfinitePlace K,
        (prescribedTraceDualFamily hξ).norm (normalizedInfinitePlacePoint w) (z w) := by
    apply Finset.sum_congr rfl
    intro w _
    let e := LinearEquiv.baseChange K (CompletedCoefficient w) _ _
      (TensorProduct.rid K (Module.Dual K E))
    have he := dualizingTensor_norm_infinite ξ.dual hξ.dual w (e (z w))
    change (prescribedTraceDualFamily hξ).norm (normalizedInfinitePlacePoint w)
      (e.symm (e (z w))) = _ at he
    rw [e.symm_apply_apply] at he
    exact he.symm
  rw [hs] at h
  exact h

/-- The actual polar is contained in the original prescribed dual-tensor product
unit ball, on exactly the same completed vector product. -/
theorem prescribedTraceDual_polar_subset_productBall
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanNormedAddCommGroup (prescribedTraceDualFamily hξ)
    letI := euclideanNormedSpace (prescribedTraceDualFamily hξ)
    arithmeticTraceTensorIsometry hξ ⁻¹' StrongDual.polar ℝ (productBall ξ 1) ⊆
      productBall (prescribedTraceDualFamily hξ) 1 := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanNormedAddCommGroup (prescribedTraceDualFamily hξ)
  let := euclideanNormedSpace (prescribedTraceDualFamily hξ)
  rw [prescribedTraceDual_polar]
  intro z hz w
  exact (Finset.single_le_sum
    (fun v _ => (prescribedTraceDualFamily hξ).norm_nonneg _ (z v))
    (Finset.mem_univ w)).trans hz

end ArakelovGeometry.NumberFieldArithmeticPolar

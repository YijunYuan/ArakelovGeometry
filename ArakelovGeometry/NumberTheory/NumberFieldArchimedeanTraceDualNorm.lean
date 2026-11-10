/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldArchimedeanTracePairing
import ArakelovGeometry.NumberTheory.NumberFieldArchimedeanWeightedEuclidean
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Operator norms of the actual Archimedean vector trace pairing

The local factor uses the canonical dual family and the original primal norm.
A phase in the actual completed field makes any nonzero evaluation positive
real without changing its norm. No metric is defined by pulling back the trace.
-/

noncomputable section
open NumberField
open scoped TensorProduct
namespace ArakelovGeometry.NumberFieldArchimedeanTraceDualNorm
open AdelicStructure NormFamily NumberFieldArchimedeanVectorDiagonal
  NumberFieldArchimedeanEuclidean NumberFieldArchimedeanWeightedEuclidean
  NumberFieldArchimedeanTrace NumberFieldArchimedeanTracePairing

variable {K : Type*} [Field K] [NumberField K]

/-- A phase in the literal completed field, for its original real scalar embedding. -/
def coefficientPhase (w : InfinitePlace K) (a : CompletedCoefficient w) :
    CompletedCoefficient w :=
  algebraMap ℝ (CompletedCoefficient w) ‖a‖ * a⁻¹

theorem coefficientPhase_mul (w : InfinitePlace K) {a : CompletedCoefficient w}
    (ha : a ≠ 0) :
    coefficientPhase w a * a = algebraMap ℝ (CompletedCoefficient w) ‖a‖ := by
  rw [coefficientPhase, mul_assoc, inv_mul_cancel₀ ha, mul_one]

theorem norm_coefficientPhase (w : InfinitePlace K) {a : CompletedCoefficient w}
    (ha : a ≠ 0) : ‖coefficientPhase w a‖ = 1 := by
  rw [coefficientPhase, norm_mul, norm_inv]
  have hr : ‖algebraMap ℝ (CompletedCoefficient w) ‖a‖‖ = ‖a‖ := by
    change ‖completedRealScalarMap w ‖a‖‖ = _
    rw [norm_completedRealScalarMap, abs_of_nonneg (norm_nonneg a)]
  rw [hr, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha)]

variable {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem localTraceDualMap_bound
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (w : InfinitePlace K)
    (f : CompletedCoefficient w ⊗[K] Module.Dual K E)
    (x : CompletedCoefficient w ⊗[K] E) :
    ‖localTraceDualMap (K := K) (E := E) w f x‖ ≤
      ((w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) f) *
        ξ.norm (normalizedInfinitePlacePoint w) x := by
  rw [localTraceDualMap_apply]
  exact (coefficientTrace_norm_bound w _).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (ξ.norm_dual_apply_le (normalizedInfinitePlacePoint w) f x) (Nat.cast_nonneg _))

/-- The actual local real trace functional with the original primal norm. -/
def localTraceCLM
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (w : InfinitePlace K)
    (f : CompletedCoefficient w ⊗[K] Module.Dual K E) :
    letI := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
    letI := fibreRealNormedSpace ξ w
    StrongDual ℝ (CompletedCoefficient w ⊗[K] E) := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  exact (localTraceDualMap (K := K) (E := E) w f).mkContinuous
    ((w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) f)
    (localTraceDualMap_bound ξ w f)

@[simp]
theorem localTraceCLM_apply
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (w : InfinitePlace K)
    (f : CompletedCoefficient w ⊗[K] Module.Dual K E)
    (x : CompletedCoefficient w ⊗[K] E) :
    localTraceCLM ξ w f x = localTraceDualMap (K := K) (E := E) w f x := rfl

theorem norm_localTraceCLM
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (w : InfinitePlace K)
    (f : CompletedCoefficient w ⊗[K] Module.Dual K E) :
    letI := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
    letI := fibreRealNormedSpace ξ w
    ‖localTraceCLM ξ w f‖ = (w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) f := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := ξ.fibreNormedSpace (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  have hn : 0 < (w.mult : ℝ) := by exact_mod_cast (InfinitePlace.mult_pos (w := w))
  apply le_antisymm
  · exact (localTraceDualMap (K := K) (E := E) w f).mkContinuous_norm_le
      (mul_nonneg (Nat.cast_nonneg _) (ξ.dual.norm_nonneg _ _))
      (localTraceDualMap_bound ξ w f)
  · have hbound (x : CompletedCoefficient w ⊗[K] E) :
        (w.mult : ℝ) * ‖dualBaseChangeEquiv K (CompletedCoefficient w) E f x‖ ≤
          ‖localTraceCLM ξ w f‖ * ‖x‖ := by
      let a := dualBaseChangeEquiv K (CompletedCoefficient w) E f x
      by_cases ha : a = 0
      · change (w.mult : ℝ) * ‖a‖ ≤ _
        rw [ha, _root_.norm_zero, mul_zero]
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · have h := (localTraceCLM ξ w f).le_opNorm (coefficientPhase w a • x)
        rw [localTraceCLM_apply, localTraceDualMap_apply, map_smul, smul_eq_mul,
          coefficientPhase_mul w ha, coefficientTrace_algebraMap,
          norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
          Real.norm_of_nonneg (norm_nonneg a),
          _root_.norm_smul, norm_coefficientPhase w ha, one_mul] at h
        exact h
    have hd := ξ.dual_norm_le (normalizedInfinitePlacePoint w) f
      (div_nonneg (norm_nonneg (localTraceCLM ξ w f)) hn.le) (by
        intro x
        change ‖dualBaseChangeEquiv K (CompletedCoefficient w) E f x‖ ≤
          (‖localTraceCLM ξ w f‖ / (w.mult : ℝ)) * ‖x‖
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hn).mpr
        nlinarith [hbound x])
    simpa only [mul_comm] using (le_div_iff₀ hn).mp hd

/-- Real finite dimensionality of a literal completed fibre, obtained from the actual product. -/
theorem finite_completedRealFibre (w : InfinitePlace K) :
    FiniteDimensional ℝ (CompletedCoefficient w ⊗[K] E) := by
  classical
  exact FiniteDimensional.of_surjective
    (LinearMap.proj w : CompletedVectorProduct K E →ₗ[ℝ] _)
    (fun x => ⟨Pi.single w x, by simp⟩)

/-- The local real inner product determined by the original Hermitian fibre norm. -/
@[instance_reducible]
def localRealInnerProduct
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (w : InfinitePlace K) :
    letI := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
    letI := fibreRealNormedSpace ξ w
    InnerProductSpace ℝ (CompletedCoefficient w ⊗[K] E) := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  apply InnerProductSpace.ofNorm ℝ
  intro x y
  change ξ.norm (normalizedInfinitePlacePoint w) (x + y) *
      ξ.norm (normalizedInfinitePlacePoint w) (x + y) +
      ξ.norm (normalizedInfinitePlacePoint w) (x - y) *
      ξ.norm (normalizedInfinitePlacePoint w) (x - y) =
    2 * (ξ.norm (normalizedInfinitePlacePoint w) x * ξ.norm (normalizedInfinitePlacePoint w) x +
      ξ.norm (normalizedInfinitePlacePoint w) y * ξ.norm (normalizedInfinitePlacePoint w) y)
  simpa only [← pow_two] using
    (NormFamily.isHermitian_iff_parallelogram.mp hξ).2
      (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w) x y

/-- Real Riesz representation for the actual local trace functional. -/
def localTraceRiesz
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (w : InfinitePlace K) (f : CompletedCoefficient w ⊗[K] Module.Dual K E) :
    CompletedCoefficient w ⊗[K] E := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  let := localRealInnerProduct hξ w
  let := finite_completedRealFibre (E := E) w
  exact (InnerProductSpace.toDual ℝ _).symm (localTraceCLM ξ w f)

theorem localTraceRiesz_inner
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (w : InfinitePlace K) (f : CompletedCoefficient w ⊗[K] Module.Dual K E)
    (x : CompletedCoefficient w ⊗[K] E) :
    letI := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
    letI := fibreRealNormedSpace ξ w
    letI := localRealInnerProduct hξ w
    inner ℝ (localTraceRiesz hξ w f) x = localTraceDualMap (K := K) (E := E) w f x := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  let := localRealInnerProduct hξ w
  let := finite_completedRealFibre (E := E) w
  exact InnerProductSpace.toDual_symm_apply

theorem norm_localTraceRiesz
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (w : InfinitePlace K) (f : CompletedCoefficient w ⊗[K] Module.Dual K E) :
    ξ.norm (normalizedInfinitePlacePoint w) (localTraceRiesz hξ w f) =
      (w.mult : ℝ) * ξ.dual.norm (normalizedInfinitePlacePoint w) f := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  let := localRealInnerProduct hξ w
  let := finite_completedRealFibre (E := E) w
  change ‖(InnerProductSpace.toDual ℝ _).symm (localTraceCLM ξ w f)‖ = _
  rw [LinearIsometryEquiv.norm_map, norm_localTraceCLM]


/-- The original local real inner product, with its fibre instances made explicit. -/
def localInner
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (w : InfinitePlace K) (x y : CompletedCoefficient w ⊗[K] E) : ℝ := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  let := localRealInnerProduct hξ w
  exact inner ℝ x y

omit [FiniteDimensional K E] in
theorem localInner_polarization
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (w : InfinitePlace K) (x y : CompletedCoefficient w ⊗[K] E) :
    localInner hξ w x y =
      (ξ.norm (normalizedInfinitePlacePoint w) (x + y) ^ 2 -
        ξ.norm (normalizedInfinitePlacePoint w) x ^ 2 -
        ξ.norm (normalizedInfinitePlacePoint w) y ^ 2) / 2 := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  let := localRealInnerProduct hξ w
  exact (real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
    x y).trans (by simp only [pow_two]; rfl)

omit [FiniteDimensional K E] in
theorem weightedInner_eq_sum
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (z x : CompletedVectorProduct K E) :
    letI := weightedNormedAddCommGroup ξ
    letI := weightedNormedSpace ξ
    letI := weightedInnerProduct hξ
    inner ℝ z x = ∑ w : InfinitePlace K, (w.mult : ℝ) * localInner hξ w (z w) (x w) := by
  let := weightedNormedAddCommGroup ξ
  let := weightedNormedSpace ξ
  let := weightedInnerProduct hξ
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  simp only [← pow_two, weighted_norm_sq, localInner_polarization, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w _
  ring


/-- The Riesz representative of the actual trace pairing in the existing weighted metric. -/
def weightedTraceRiesz
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) : CompletedVectorProduct K E :=
  fun w => (w.mult : ℝ)⁻¹ • localTraceRiesz hξ w (f w)

theorem norm_weightedTraceRiesz_coordinate
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) (w : InfinitePlace K) :
    ξ.norm (normalizedInfinitePlacePoint w) (weightedTraceRiesz hξ f w) =
      ξ.dual.norm (normalizedInfinitePlacePoint w) (f w) := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  have hn : 0 < (w.mult : ℝ) := by exact_mod_cast (InfinitePlace.mult_pos (w := w))
  change ‖(w.mult : ℝ)⁻¹ • localTraceRiesz hξ w (f w)‖ = _
  rw [_root_.norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  change (w.mult : ℝ)⁻¹ * ξ.norm _ (localTraceRiesz hξ w (f w)) = _
  rw [norm_localTraceRiesz, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

theorem weightedTraceRiesz_inner
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) (x : CompletedVectorProduct K E) :
    letI := weightedNormedAddCommGroup ξ
    letI := weightedNormedSpace ξ
    letI := weightedInnerProduct hξ
    inner ℝ (weightedTraceRiesz hξ f) x = tracePairing (K := K) (E := E) f x := by
  let := weightedNormedAddCommGroup ξ
  let := weightedNormedSpace ξ
  let := weightedInnerProduct hξ
  rw [weightedInner_eq_sum, tracePairing_apply]
  apply Finset.sum_congr rfl
  intro w _
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  let := localRealInnerProduct hξ w
  change (w.mult : ℝ) * inner ℝ ((w.mult : ℝ)⁻¹ • localTraceRiesz hξ w (f w)) (x w) = _
  rw [real_inner_smul_left, localTraceRiesz_inner, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast (InfinitePlace.mult_pos (w := w)).ne'), one_mul]
  rfl

theorem weightedTraceRiesz_norm_sq
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    letI := weightedNormedAddCommGroup ξ
    ‖weightedTraceRiesz hξ f‖ ^ 2 = ∑ w : InfinitePlace K,
      (w.mult : ℝ) * (ξ.dual.norm (normalizedInfinitePlacePoint w) (f w)) ^ 2 := by
  let := weightedNormedAddCommGroup ξ
  rw [weighted_norm_sq]
  simp only [norm_weightedTraceRiesz_coordinate]

/-- The original trace pairing, continuously on the already defined weighted primal norm. -/
def tracePairingCLM
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    letI := weightedNormedAddCommGroup ξ
    letI := weightedNormedSpace ξ
    StrongDual ℝ (CompletedVectorProduct K E) := by
  let := weightedNormedAddCommGroup ξ
  let := weightedNormedSpace ξ
  exact LinearMap.toContinuousLinearMap (tracePairing (K := K) (E := E) f)

@[simp]
theorem tracePairingCLM_apply
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (f : CompletedVectorProduct K (Module.Dual K E)) (x : CompletedVectorProduct K E) :
    tracePairingCLM ξ f x = tracePairing (K := K) (E := E) f x := rfl

theorem norm_tracePairingCLM_sq
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    letI := weightedNormedAddCommGroup ξ
    letI := weightedNormedSpace ξ
    ‖tracePairingCLM ξ f‖ ^ 2 = ∑ w : InfinitePlace K,
      (w.mult : ℝ) * (ξ.dual.norm (normalizedInfinitePlacePoint w) (f w)) ^ 2 := by
  let := weightedNormedAddCommGroup ξ
  let := weightedNormedSpace ξ
  let := weightedInnerProduct hξ
  have he : tracePairingCLM ξ f =
      InnerProductSpace.toDual ℝ _ (weightedTraceRiesz hξ f) := by
    ext x
    exact (weightedTraceRiesz_inner hξ f x).symm
  rw [he, LinearIsometryEquiv.norm_map]
  exact weightedTraceRiesz_norm_sq hξ f

theorem norm_tracePairingCLM
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    letI := weightedNormedAddCommGroup ξ
    letI := weightedNormedSpace ξ
    letI := weightedNormedAddCommGroup ξ.dual
    ‖tracePairingCLM ξ f‖ = ‖f‖ := by
  let := weightedNormedAddCommGroup ξ
  let := weightedNormedSpace ξ
  let := weightedNormedAddCommGroup ξ.dual
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_tracePairingCLM_sq hξ, weighted_norm_sq]

theorem norm_tracePairingCLM_sqrt
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) :
    letI := weightedNormedAddCommGroup ξ
    letI := weightedNormedSpace ξ
    ‖tracePairingCLM ξ f‖ = Real.sqrt (∑ w : InfinitePlace K,
      (w.mult : ℝ) * (ξ.dual.norm (normalizedInfinitePlacePoint w) (f w)) ^ 2) := by
  let := weightedNormedAddCommGroup ξ
  let := weightedNormedSpace ξ
  rw [← norm_tracePairingCLM_sq hξ, Real.sqrt_sq (norm_nonneg _)]

/-- Actual trace duality as a real isometry between the independently defined weighted metrics. -/
def traceDualIsometry
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := weightedNormedAddCommGroup ξ
    letI := weightedNormedSpace ξ
    letI := weightedNormedAddCommGroup ξ.dual
    letI := weightedNormedSpace ξ.dual
    CompletedVectorProduct K (Module.Dual K E) ≃ₗᵢ[ℝ]
      StrongDual ℝ (CompletedVectorProduct K E) := by
  let := weightedNormedAddCommGroup ξ
  let := weightedNormedSpace ξ
  let := weightedNormedAddCommGroup ξ.dual
  let := weightedNormedSpace ξ.dual
  exact { (tracePairingEquiv (K := K) (E := E)).trans LinearMap.toContinuousLinearMap with
    norm_map' := norm_tracePairingCLM hξ }

@[simp]
theorem traceDualIsometry_apply
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : CompletedVectorProduct K (Module.Dual K E)) (x : CompletedVectorProduct K E) :
    traceDualIsometry hξ f x = tracePairing (K := K) (E := E) f x := rfl

theorem traceDualIsometry_original
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (f : Module.Dual K E) (x : E) :
    traceDualIsometry hξ (vectorDiagonalMap (K := K) f) (vectorDiagonalMap (K := K) x) =
      (Algebra.trace ℚ K (f x) : ℝ) := by
  rw [traceDualIsometry_apply, tracePairing_original]

theorem traceDualIsometry_integral
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (M : Submodule (𝓞 K) E) (f : NumberFieldIntegralTraceDual.integralTraceDual M) (m : M) :
    traceDualIsometry hξ (vectorDiagonalMap (K := K) (f : Module.Dual K E))
      (vectorDiagonalMap (K := K) (m : E)) ∈ LinearMap.range (Algebra.linearMap ℤ ℝ) := by
  refine ⟨NumberFieldIntegralTraceDual.traceRestriction M f m, ?_⟩
  change (NumberFieldIntegralTraceDual.traceRestriction M f m : ℝ) = _
  rw [traceDualIsometry_original]
  exact_mod_cast NumberFieldIntegralTraceDual.traceRestriction_apply M f m

end ArakelovGeometry.NumberFieldArchimedeanTraceDualNorm

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Archimedean.VectorDiagonal
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Topology.Sheaves.Init
/-! # Trace on actual normalized Archimedean coefficient fields

The canonical real scalar action and ordinary completed norms are retained.
The literal product trace sums the real coefficients and twice the complex
real parts. Grouping the separable embedding trace proves its value on original
diagonal scalars. Exact local operator factors equal the actual place masses.
-/

@[expose] public section

open NumberField
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NumberFieldArchimedeanTrace
open NumberFieldArchimedeanDiagonal NumberFieldArchimedeanVectorDiagonal AdelicStructure
variable {K : Type*} [Field K] [NumberField K]
open scoped Classical in
def coefficientTrace (w : InfinitePlace K) : CompletedCoefficient w →ₗ[ℝ] ℝ where
  toFun z := if hw : w.IsReal then normalizedRealCompletionEquiv hw z
    else 2 * (normalizedComplexCompletionEquiv
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) z).re
  map_add' z z' := by
    classical
    split_ifs <;> simp [map_add, mul_add]
  map_smul' r z := by
    classical
    change (if hw : w.IsReal then
      normalizedRealCompletionEquiv hw (completedRealScalarMap w r * z)
      else 2 * (normalizedComplexCompletionEquiv
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)
        (completedRealScalarMap w r * z)).re) = _
    split_ifs with hw
    · simp [completedRealScalarMap, hw, smul_eq_mul]
    · simp [completedRealScalarMap, hw, smul_eq_mul, Complex.mul_re]
      ring
theorem coefficientTrace_real {w : InfinitePlace K} (hw : w.IsReal)
    (z : CompletedCoefficient w) :
    coefficientTrace w z = normalizedRealCompletionEquiv hw z := by
  simp [coefficientTrace, hw]
theorem coefficientTrace_complex {w : InfinitePlace K} (hw : w.IsComplex)
    (z : CompletedCoefficient w) :
    coefficientTrace w z = 2 * (normalizedComplexCompletionEquiv hw z).re := by
  simp [coefficientTrace, InfinitePlace.not_isReal_iff_isComplex.mpr hw]
theorem coefficientTrace_algebraMap (w : InfinitePlace K) (r : ℝ) :
    coefficientTrace w (algebraMap ℝ (CompletedCoefficient w) r) = (w.mult : ℝ) * r := by
  classical
  change coefficientTrace w (completedRealScalarMap w r) = _
  by_cases hw : w.IsReal
  · simp [coefficientTrace, completedRealScalarMap, hw, InfinitePlace.mult]
  · simp [coefficientTrace, completedRealScalarMap, hw, InfinitePlace.mult]
theorem coefficientTrace_original (w : InfinitePlace K) (x : K) :
    coefficientTrace w (algebraMap K (CompletedCoefficient w) x) =
      (w.mult : ℝ) * (w.embedding x).re := by
  classical
  by_cases hw : w.IsReal
  · rw [coefficientTrace_real hw, normalizedRealCompletionEquiv_coe,
      hw.mult_eq_one, Nat.cast_one, one_mul]
    exact (congrArg Complex.re (InfinitePlace.embedding_of_isReal_apply hw x)).symm
  · rw [coefficientTrace_complex (InfinitePlace.not_isReal_iff_isComplex.mp hw),
      normalizedComplexCompletionEquiv_coe,
      (InfinitePlace.not_isReal_iff_isComplex.mp hw).mult_eq_two, Nat.cast_ofNat]
theorem coefficientTrace_norm_bound (w : InfinitePlace K) (z : CompletedCoefficient w) :
    ‖coefficientTrace w z‖ ≤ (w.mult : ℝ) * ‖z‖ := by
  classical
  by_cases hw : w.IsReal
  · rw [coefficientTrace_real hw, hw.mult_eq_one, Nat.cast_one, one_mul,
      norm_normalizedRealCompletionEquiv hw]
  · rw [coefficientTrace_complex (InfinitePlace.not_isReal_iff_isComplex.mp hw),
      (InfinitePlace.not_isReal_iff_isComplex.mp hw).mult_eq_two, Nat.cast_ofNat,
      norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (by
      rw [← norm_normalizedComplexCompletionEquiv
        (InfinitePlace.not_isReal_iff_isComplex.mp hw) z]
      exact Complex.abs_re_le_norm _) (by norm_num)
def coefficientTraceCLM (w : InfinitePlace K) : CompletedCoefficient w →L[ℝ] ℝ :=
  (coefficientTrace w).mkContinuous (w.mult : ℝ) (coefficientTrace_norm_bound w)
theorem coefficientTraceCLM_apply (w : InfinitePlace K) (z : CompletedCoefficient w) :
    coefficientTraceCLM w z = coefficientTrace w z := rfl
theorem norm_coefficientTraceCLM (w : InfinitePlace K) :
    ‖coefficientTraceCLM w‖ = (w.mult : ℝ) := by
  apply le_antisymm
  · exact (coefficientTraceCLM w).opNorm_le_bound (Nat.cast_nonneg _)
      (coefficientTrace_norm_bound w)
  · have h := (coefficientTraceCLM w).le_opNorm 1
    rw [coefficientTraceCLM_apply, show (1 : CompletedCoefficient w) =
      algebraMap ℝ (CompletedCoefficient w) 1 from (map_one _).symm,
      coefficientTrace_algebraMap] at h
    simpa [Real.norm_of_nonneg (Nat.cast_nonneg w.mult)] using h
open scoped Classical in
def totalTrace : CompletedScalarProduct K →ₗ[ℝ] ℝ :=
  ∑ w : InfinitePlace K, (coefficientTrace w).comp (LinearMap.proj w)
theorem totalTrace_apply (z : CompletedScalarProduct K) :
    totalTrace z = ∑ w : InfinitePlace K, coefficientTrace w (z w) := by
  classical
  simp [totalTrace]
theorem totalTrace_algebraMap (r : ℝ) :
    totalTrace (algebraMap ℝ (CompletedScalarProduct K) r) =
      (Module.finrank ℚ K : ℝ) * r := by
  classical
  rw [totalTrace_apply]
  simp only [Pi.algebraMap_apply, coefficientTrace_algebraMap, ← Finset.sum_mul]
  rw [← Nat.cast_sum, InfinitePlace.sum_mult_eq]

omit [NumberField K] in
theorem embedding_re_of_same_place (w : InfinitePlace K) (φ : K →+* ℂ)
    (h : InfinitePlace.mk φ = w) (x : K) :
    (φ x).re = (w.embedding x).re := by
  have h' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding :=
    h.trans (InfinitePlace.mk_embedding w).symm
  rcases InfinitePlace.mk_eq_iff.mp h' with h' | h'
  · rw [h']
  · have := congrArg (fun ψ : K →+* ℂ => (ψ x).re) h'
    simpa [ComplexEmbedding.conjugate_coe_eq] using this

theorem trace_eq_sum_infinite_embedding_re (x : K) :
    (Algebra.trace ℚ K x : ℝ) =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * (w.embedding x).re := by
  classical
  have ht := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := x)
  have hr : (Algebra.trace ℚ K x : ℝ) = ∑ φ : K →+* ℂ, (φ x).re := by
    have hs : (∑ φ : K →+* ℂ, φ x) = ∑ σ : K →ₐ[ℚ] ℂ, σ x :=
      Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun _ => rfl)
    rw [← hs] at ht
    have hh := congrArg Complex.re ht
    simpa using hh
  rw [hr, ← Finset.univ.sum_fiberwise (fun φ : K →+* ℂ => InfinitePlace.mk φ)]
  apply Finset.sum_congr rfl
  intro w _
  calc
    (∑ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w), (φ x).re) =
        ∑ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
          (w.embedding x).re := by
      apply Finset.sum_congr rfl
      intro φ hφ
      exact embedding_re_of_same_place w φ (Finset.mem_filter.mp hφ).2 x
    _ = (w.mult : ℝ) * (w.embedding x).re := by
      rw [Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

theorem totalTrace_original (x : K) :
    totalTrace (algebraMap K (CompletedScalarProduct K) x) =
      (Algebra.trace ℚ K x : ℝ) := by
  rw [totalTrace_apply, trace_eq_sum_infinite_embedding_re]
  apply Finset.sum_congr rfl
  intro w _
  exact coefficientTrace_original w x

theorem totalTrace_tensor (r : ℝ) (x : K) :
    totalTrace (completedScalarTensorEquiv (r ⊗ₜ[ℚ] x)) =
      r * (Algebra.trace ℚ K x : ℝ) := by
  rw [completedScalarTensorEquiv_tmul, ← Algebra.smul_def, map_smul,
    totalTrace_original, smul_eq_mul]

theorem totalTrace_norm_bound (z : CompletedScalarProduct K) :
    ‖totalTrace z‖ ≤ (Module.finrank ℚ K : ℝ) * ‖z‖ := by
  classical
  rw [totalTrace_apply]
  calc
    ‖∑ w : InfinitePlace K, coefficientTrace w (z w)‖ ≤
        ∑ w : InfinitePlace K, ‖coefficientTrace w (z w)‖ := norm_sum_le _ _
    _ ≤ ∑ w : InfinitePlace K, (w.mult : ℝ) * ‖z w‖ :=
      Finset.sum_le_sum (fun w _ => coefficientTrace_norm_bound w (z w))
    _ ≤ ∑ w : InfinitePlace K, (w.mult : ℝ) * ‖z‖ :=
      Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm z w)
        (Nat.cast_nonneg _))
    _ = (Module.finrank ℚ K : ℝ) * ‖z‖ := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]

def totalTraceCLM : CompletedScalarProduct K →L[ℝ] ℝ :=
  totalTrace.mkContinuous (Module.finrank ℚ K : ℝ) totalTrace_norm_bound

theorem totalTraceCLM_apply (z : CompletedScalarProduct K) :
    totalTraceCLM z = totalTrace z := rfl

theorem totalTrace_one :
    totalTrace (1 : CompletedScalarProduct K) = (Module.finrank ℚ K : ℝ) := by
  simpa only [map_one, mul_one] using totalTrace_algebraMap (K := K) 1

theorem norm_totalTraceCLM :
    ‖totalTraceCLM (K := K)‖ = (Module.finrank ℚ K : ℝ) := by
  apply le_antisymm
  · exact (totalTraceCLM (K := K)).opNorm_le_bound
      (Nat.cast_nonneg (Module.finrank ℚ K)) (totalTrace_norm_bound (K := K))
  · have h := (totalTraceCLM (K := K)).le_opNorm 1
    rw [totalTraceCLM_apply, totalTrace_one] at h
    simpa [Real.norm_of_nonneg (Nat.cast_nonneg (Module.finrank ℚ K))] using h


theorem norm_coefficientTraceCLM_eq_mass (w : InfinitePlace K) :
    ‖coefficientTraceCLM w‖ =
      ((normalizedNumberFieldAdelicStructure K).v {normalizedInfinitePlacePoint w}).toReal := by
  rw [norm_coefficientTraceCLM, normalizedInfinitePlacePoint,
    normalizedNumberFieldAdelicStructure_v_infinitePlace,
    ENNReal.toReal_natCast]

theorem totalTrace_real_eq_mass (r : ℝ) :
    totalTrace (algebraMap ℝ (CompletedScalarProduct K) r) =
      ((normalizedNumberFieldAdelicStructure K).v
        (normalizedNumberFieldAdelicStructure K).Ωinf).toReal * r := by
  rw [totalTrace_algebraMap, normalizedNumberFieldAdelicStructure_v_Ωinf,
    ENNReal.toReal_natCast]

theorem totalTrace_original_mul (x y : K) :
    totalTrace (algebraMap K (CompletedScalarProduct K) x *
      algebraMap K (CompletedScalarProduct K) y) = (Algebra.trace ℚ K (x * y) : ℝ) := by
  rw [← map_mul, totalTrace_original]

theorem coefficientTrace_complex_I {w : InfinitePlace K} (hw : w.IsComplex) :
    coefficientTrace w ((normalizedComplexCompletionEquiv hw).symm Complex.I) = 0 := by
  rw [coefficientTrace_complex hw, RingEquiv.apply_symm_apply, Complex.I_re, mul_zero]

theorem norm_complex_I {w : InfinitePlace K} (hw : w.IsComplex) :
    ‖(normalizedComplexCompletionEquiv hw).symm Complex.I‖ = 1 := by
  rw [← norm_normalizedComplexCompletionEquiv hw, RingEquiv.apply_symm_apply, Complex.norm_I]

end ArakelovGeometry.NumberFieldArchimedeanTrace

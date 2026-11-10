/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.LineVectorDegree
public import ArakelovGeometry.NumberTheory.NumberFieldTraceDualizingLineCovolume

/-! # The actual codifferent quotient by the included integer ring -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldCodifferentIndex

open AdelicStructure NumberFieldCodifferentDual NumberFieldTraceDualizingLine
  NumberFieldTraceDualizingLineCovolume NumberFieldFullLattice
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
attribute [local instance 3000] AddCommGroup.toIntModule
attribute [local instance] normalizedNumberFieldAdelicStructure_isProper
attribute [local instance] NumberFieldFullLattice.degreeCovolumeDiscrete

variable (K : Type*) [Field K] [NumberField K]

/-- The actual unit of K as an element of its literal trace codifferent. -/
def codifferentOne : codifferentModule K := ⟨1, one_mem_codifferent K⟩

/-- The actual O_K-linear inclusion of the integer ring into its codifferent. -/
def integerToCodifferent : 𝓞 K →ₗ[𝓞 K] codifferentModule K :=
  LinearMap.toSpanSingleton (𝓞 K) (codifferentModule K) (codifferentOne K)

@[simp]
theorem integerToCodifferent_apply (a : 𝓞 K) :
    (integerToCodifferent K a : K) = (a : K) := by
  simp [integerToCodifferent, codifferentOne]

theorem integerToCodifferent_injective : Function.Injective (integerToCodifferent K) := by
  intro a b h
  apply RingOfIntegers.ext
  exact (integerToCodifferent_apply K a).symm.trans
    ((congrArg (fun x : codifferentModule K => (x : K)) h).trans
      (integerToCodifferent_apply K b))

/-- The included integer ring is the O_K-span of one, not its integer span. -/
theorem integerToCodifferent_range :
    (integerToCodifferent K).range = Submodule.span (𝓞 K) {codifferentOne K} :=
  LinearMap.range_toSpanSingleton (codifferentOne K)

private theorem codifferentOne_ne_zero : codifferentOne K ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg (fun x : codifferentModule K => (x : K)) h)

/-- Actual positive cardinality, proved by finite-index arithmetic of a full integral line. -/
theorem codifferentQuotient_card_pos :
    0 < Nat.card (codifferentModule K ⧸ Submodule.span (𝓞 K) {codifferentOne K}) :=
  line_cyclicQuotient_card_pos (codifferentModule K) (codifferent_fg K)
    (Module.finrank_self K) (codifferentOne K) (codifferentOne_ne_zero K)

/-- Actual finiteness of the native O_K-module quotient by the included integer ring. -/
theorem codifferentQuotient_finite :
    Finite (codifferentModule K ⧸ Submodule.span (𝓞 K) {codifferentOne K}) :=
  line_cyclicQuotient_finite (codifferentModule K) (codifferent_fg K)
    (Module.finrank_self K) (codifferentOne K) (codifferentOne_ne_zero K)

/-- The actual completed codifferent finite gauges compute its native quotient index. -/
theorem dualizingLine_finite_integral :
    (∫ ω in (normalizedNumberFieldAdelicStructure K).Ωfin,
      -(dualizingLine K).toNormFamily.logNorm 1 ω
        ∂(normalizedNumberFieldAdelicStructure K).v) =
      Real.log (Nat.card
        (codifferentModule K ⧸ Submodule.span (𝓞 K) {codifferentOne K})) := by
  have hf : IntegrableOn (fun ω => -(dualizingLine K).toNormFamily.logNorm 1 ω)
      (normalizedNumberFieldAdelicStructure K).Ωfin
      (normalizedNumberFieldAdelicStructure K).v :=
    ((dualizingLine K).integrable_logNorm (1 : K)).neg.integrableOn
  rw [normalized_finite_integral_eq_tsum _ hf]
  have h := line_completedGauge_finite_log_index (codifferentModule K)
    (codifferent_fg K) (codifferent_full K) (Module.finrank_self K)
    (codifferentOne K) (codifferentOne_ne_zero K)
  convert h using 1
  apply tsum_congr
  intro p
  rw [NormFamily.logNorm, dualizingLine_norm_prime]
  rfl

/-- Actual infinite-place masses and prescribed generator norms give the factor two
at each complex place in the trace-generator logarithmic integral. -/
theorem dualizingLine_infinite_integral :
    (∫ ω in (normalizedNumberFieldAdelicStructure K).Ωinf,
      (dualizingLine K).toNormFamily.logNorm 1 ω
        ∂(normalizedNumberFieldAdelicStructure K).v) =
      2 * (InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 := by
  classical
  rw [normalized_infinite_integral_eq_sum]
  simp only [NormFamily.logNorm, dualizingLine_norm_generator]
  have hs : (∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w.mult : ℝ)) =
      ∑ w : InfinitePlace K, if w.IsComplex then 2 * Real.log 2 else 0 := by
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : w.IsComplex
    · simp [hw, hw.mult_eq_two]
    · have hr := InfinitePlace.not_isComplex_iff_isReal.mp hw
      simp [hw, hr.mult_eq_one]
  rw [hs, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype]
  change (InfinitePlace.nrComplexPlaces K : ℝ) * (2 * Real.log 2) = _
  ring

/-- The actual native O_K-quotient cardinal logarithm equals the absolute
number-field discriminant logarithm, derived from actual degree and generator gauges. -/
theorem codifferentQuotient_log_card :
    Real.log (Nat.card
      (codifferentModule K ⧸ Submodule.span (𝓞 K) {codifferentOne K})) =
      Real.log |(NumberField.discr K : ℝ)| := by
  have hd := (dualizingLine K).degree_eq_vectorDegree_of_finrank_one (Or.inl inferInstance)
    normalizedNumberFieldArchimedeanCompletions (Module.finrank_self K) ⟨1, one_ne_zero⟩
  rw [AdelicVectorBundle.vectorDegree, NormFamily.vectorDegree_eq_neg_integral,
    dualizingLine_degree] at hd
  have hs := integral_add_compl (normalizedNumberFieldAdelicStructure K).measurableSet_Ωinf
    ((dualizingLine K).integrable_logNorm (1 : K))
  have hc : (normalizedNumberFieldAdelicStructure K).Ωinfᶜ =
      (normalizedNumberFieldAdelicStructure K).Ωfin := by
    simp only [Ωinf, Ωfin, Set.compl_ofPred, not_not]
  rw [hc, dualizingLine_infinite_integral] at hs
  have hf := dualizingLine_finite_integral K
  rw [integral_neg] at hf
  linarith

/-- The finite cardinality is computed for J/(O_K*1), the actual included integer ring. -/
theorem codifferentQuotient_card :
    Nat.card (codifferentModule K ⧸ Submodule.span (𝓞 K) {codifferentOne K}) =
      (NumberField.discr K).natAbs := by
  have hp : (0 : ℝ) < Nat.card
      (codifferentModule K ⧸ Submodule.span (𝓞 K) {codifferentOne K}) := by
    exact_mod_cast codifferentQuotient_card_pos K
  have hd := NumberFieldActualIntegerCovolume.discriminant_abs_pos K
  have h := Real.strictMonoOn_log.injOn hp hd (codifferentQuotient_log_card K)
  have ha : ((NumberField.discr K).natAbs : ℝ) = |(NumberField.discr K : ℝ)| :=
    by
      simpa only [Int.cast_natCast, Int.cast_abs] using
        congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (NumberField.discr K))
  exact_mod_cast h.trans ha.symm

/-- The identical actual cardinality, stated for the range of the original integer inclusion. -/
theorem codifferentQuotient_range_card :
    Nat.card (codifferentModule K ⧸ (integerToCodifferent K).range) =
      (NumberField.discr K).natAbs := by
  rw [integerToCodifferent_range]
  exact codifferentQuotient_card K

end ArakelovGeometry.NumberFieldCodifferentIndex

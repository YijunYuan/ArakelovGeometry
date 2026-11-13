/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Basic

import ArakelovGeometry.MeasureTheory.Measure.PositiveAtomic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Finite weighted prime thresholds for actual norm families

The integrability step in the proof of Chen–Moriwaki Proposition 4.4.6
(PDF page 308). Positive atomic masses upgrade an envelope to a pointwise
bound. The norm-density measure then makes every positive weighted threshold
finite, without assuming countability or coherence. The arithmetic uniformizer
gap is a separate hypothesis in the rounded-order consumer.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  {μ : Measure X} {f : X → ℝ}

/-- Integrable upper envelopes have only finitely many deviations of a fixed
positive size after weighting by the actual singleton masses. -/
theorem HasIntegrableUpperBound.finite_weighted_threshold
    (hf : HasIntegrableUpperBound f μ) (hμ : ∀ x, 0 < μ {x})
    {ε : ℝ} (hε : 0 < ε) : {x | ε ≤ μ.real {x} * f x}.Finite := by
  obtain ⟨A, hA, hfA⟩ := hf
  have hpoint := (ae_iff_forall_of_pos_singletons hμ (fun x => f x ≤ A x)).mp hfA
  let ν := μ.withDensity (fun x => ‖A x‖ₑ)
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hA.hasFiniteIntegral.ne
  have hfinite : {x | ENNReal.ofReal ε ≤ ν {x}}.Finite :=
    Measure.finite_const_le_meas_of_disjoint_iUnion ν (ENNReal.ofReal_pos.mpr hε)
      (fun x => measurableSet_singleton x)
      (fun _ _ h => Set.disjoint_singleton.mpr h) (measure_ne_top ν _)
  refine hfinite.subset ?_
  intro x hx
  change ENNReal.ofReal ε ≤ μ.withDensity (fun y => ‖A y‖ₑ) {x}
  rw [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton]
  have hbound : f x ≤ ‖A x‖ := (hpoint x).trans (by simpa using le_abs_self (A x))
  calc
    ENNReal.ofReal ε ≤ ENNReal.ofReal (μ.real {x} * ‖A x‖) :=
      ENNReal.ofReal_le_ofReal (hx.trans (mul_le_mul_of_nonneg_left hbound
        ENNReal.toReal_nonneg))
    _ = ENNReal.ofReal (μ.real {x}) * ‖A x‖ₑ := by
      rw [ENNReal.ofReal_mul (show 0 ≤ μ.real {x} from ENNReal.toReal_nonneg),
        ofReal_norm]
    _ ≤ μ {x} * ‖A x‖ₑ := mul_le_mul' ENNReal.ofReal_toReal_le le_rfl
    _ = ‖A x‖ₑ * μ {x} := mul_comm _ _

namespace NormFamily

universe u w

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E]
  [MeasurableSingletonClass S.Ω] {ξ : NormFamily S E}

/-- Lower domination controls actual small completed rational norms at every
fixed positive weighted logarithmic threshold. -/
theorem IsLowerDominated.finite_weighted_small_norm_threshold
    (hξ : ξ.IsLowerDominated) [hμ : S.HasPositiveSingletons]
    {x : E} (hx : x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    {ω | ε ≤ S.v.real {ω} * (-ξ.logNorm x ω)}.Finite :=
  (hξ x hx).neg.finite_weighted_threshold hμ hε

/-- Source domination implies the small-norm threshold bound through the
actual dual evaluation lower envelope. -/
theorem IsDominated.finite_weighted_small_norm_threshold [FiniteDimensional K E]
    (hξ : ξ.IsDominated) [hμ : S.HasPositiveSingletons]
    {x : E} (hx : x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    {ω | ε ≤ S.v.real {ω} * (-ξ.logNorm x ω)}.Finite :=
  hξ.lower.finite_weighted_small_norm_threshold hx hε

/-- The negative support of the source's rounded order requirement is finite
once the actual measure and local logarithmic scale have a positive gap. -/
theorem IsLowerDominated.finite_negative_rounded_orders
    (hξ : ξ.IsLowerDominated) [hμ : S.HasPositiveSingletons]
    {x : E} (hx : x ≠ 0) (T : Set S.Ω) (γ : S.Ω → ℝ)
    (hγ : ∀ ω ∈ T, 0 < γ ω) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ ω ∈ T, ε ≤ S.v.real {ω} * γ ω) :
    {ω | ω ∈ T ∧ ⌈ξ.logNorm x ω / γ ω⌉ < (0 : ℤ)}.Finite := by
  refine (hξ.finite_weighted_small_norm_threshold hx hε).subset ?_
  intro ω hω
  obtain ⟨hωT, hnegative⟩ := hω
  have hceil : (⌈ξ.logNorm x ω / γ ω⌉ : ℤ) ≤ -1 := by omega
  have hdiv : ξ.logNorm x ω / γ ω ≤ -1 :=
    (Int.le_ceil _).trans (by exact_mod_cast hceil)
  have hlog : γ ω ≤ -ξ.logNorm x ω := by
    have := (div_le_iff₀ (hγ ω hωT)).mp hdiv
    linarith
  exact (hgap ω hωT).trans (mul_le_mul_of_nonneg_left hlog ENNReal.toReal_nonneg)

end NormFamily
end ArakelovGeometry

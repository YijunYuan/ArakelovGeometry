/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Determinant.Basic

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.Determinant.Comparison
import ArakelovGeometry.AdelicVectorBundle.Determinant.PairingLocal
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Approximation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Local bounds for determinant discrepancy

Actual inner-product majorants and determinant order/scaling give the
sharp Archimedean discrepancy bound. Finite places have discrepancy one
even when the original vector norm is not ultrametric.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w

/-- The seminorm of an actual positive-definite inner-product core, with
its given scalar action. -/
def innerProductCoreSeminorm {L V : Type*} [RCLike L] [AddCommGroup V] [Module L V]
    (c : InnerProductSpace.Core L V) : Seminorm L V :=
  @normSeminorm L V _ c.toNormedAddCommGroup.toSeminormedAddCommGroup
    InnerProductSpace.Core.toNormedSpace

theorem innerProductCoreSeminorm_apply {L V : Type*} [RCLike L]
    [AddCommGroup V] [Module L V] (c : InnerProductSpace.Core L V) (x : V) :
    innerProductCoreSeminorm c x = Real.sqrt (RCLike.re (c.inner x x)) := rfl

theorem innerProductCoreSeminorm_eq_zero_iff {L V : Type*} [RCLike L]
    [AddCommGroup V] [Module L V] (c : InnerProductSpace.Core L V) (x : V) :
    innerProductCoreSeminorm c x = 0 ↔ x = 0 := by
  let := c.toNormedAddCommGroup
  change ‖x‖ = 0 ↔ x = 0
  exact norm_eq_zero

namespace NormFamily

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E]

/-- Replace one actual fibre norm by another separated seminorm. -/
def withFibreNorm (ξ : NormFamily S E) (ω : S.Ω)
    (p : Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E))
    (hp : ∀ x, p x = 0 ↔ x = 0) : NormFamily S E := by
  classical
  refine ⟨Function.update ξ.norm ω p, fun ω' x ↦ ?_⟩
  by_cases h : ω' = ω
  · subst ω'
    simpa only [Function.update_self] using hp x
  · simpa only [Function.update_of_ne h] using ξ.norm_eq_zero_iff ω' x

@[simp]
theorem withFibreNorm_norm (ξ : NormFamily S E) (ω : S.Ω)
    (p : Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E))
    (hp : ∀ x, p x = 0 ↔ x = 0) (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.withFibreNorm ω p hp).norm ω x = p x := by
  classical
  change (Function.update ξ.norm ω p ω) x = p x
  rw [Function.update_self]

variable [FiniteDimensional K E]

/-- A local norm majorant with exact determinant pairing bounds discrepancy
by the rank power of its norm comparison constant. -/
theorem determinantDiscrepancy_le_pow_of_majorant (ξ η : NormFamily S E) (ω : S.Ω)
    {C : ℝ} (hC : 0 < C)
    (hl : ∀ x, ξ.norm ω x ≤ η.norm ω x)
    (hu : ∀ x, η.norm ω x ≤ C * ξ.norm ω x)
    (hp : η.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) *
      η.dual.determinant.norm ω (1 ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E)) = 1) :
    ξ.determinantDiscrepancy ω ≤ C ^ Module.finrank K E := by
  have h1 := η.determinant_norm_le_mul_pow ξ ω hC hu
    (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E))
  have h2 := η.dual.determinant_norm_mono ξ.dual ω
    (ξ.dual_norm_antitone η ω hl)
    (1 ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E))
  have hprod := mul_le_mul h1 h2 (η.dual.determinant.norm_nonneg ω _)
    (mul_nonneg (pow_pos hC _).le (ξ.determinant.norm_nonneg ω _))
  rw [hp] at hprod
  rw [determinantDiscrepancy, ← one_div, div_le_iff₀
    (mul_pos (ξ.determinant.norm_rational_pos ω determinantGenerator_ne_zero)
      (ξ.dual.determinant.norm_rational_pos ω dualDeterminantGenerator_ne_zero))]
  calc
    (1 : ℝ) ≤ (C ^ Module.finrank K E * ξ.determinant.norm ω
        (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E))) *
        ξ.dual.determinant.norm ω
          (1 ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E)) := hprod
    _ = _ := by ring

/-- The source finite-place identity holds for every vector norm. -/
theorem determinantDiscrepancy_eq_one_finite (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) : ξ.determinantDiscrepancy ω = 1 := by
  have h := ξ.norm_completedDeterminantPairing_eq_finite ω hω
    (1 ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E))
    (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E))
  rw [completedDeterminantGenerator_pairing, norm_one] at h
  rw [determinantDiscrepancy, ← h, inv_one]

/-- An actual local inner product makes determinant discrepancy one,
independently of norms at other places. -/
theorem determinantDiscrepancy_eq_one_of_innerProductCore (ξ : NormFamily S E)
    (ω : S.Ω) [IsRCLikeNormedField (S.ϕ ω).Completion] :
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    ∀ (c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E)),
      (∀ x, (ξ.norm ω x) ^ 2 = RCLike.re (c.inner x x)) →
      ξ.determinantDiscrepancy ω = 1 := by
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  intro c hc
  have h := ξ.norm_completedDeterminantPairing_eq_of_innerProductCore ω c hc
    (1 ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E))
    (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E))
  rw [completedDeterminantGenerator_pairing, norm_one] at h
  rw [determinantDiscrepancy, ← h, inv_one]

/-- The sharp rank bound follows from the actual local John core and
determinant order/scaling, including rank zero. -/
theorem determinantDiscrepancy_le_sqrt_finrank_pow (ξ : NormFamily S E)
    (ω : S.Ω) [IsRCLikeNormedField (S.ϕ ω).Completion] :
    ξ.determinantDiscrepancy ω ≤
      Real.sqrt (Module.finrank K E) ^ Module.finrank K E := by
  by_cases hr : Module.finrank K E = 0
  · rw [ξ.determinantDiscrepancy_eq_one_of_finrank_eq_zero hr, hr, pow_zero]
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  obtain ⟨c, hc⟩ := ξ.exists_archimedean_john_innerProductCore ω
  let p := innerProductCoreSeminorm c
  let η := ξ.withFibreNorm ω p (innerProductCoreSeminorm_eq_zero_iff c)
  have hn (x : (S.ϕ ω).Completion ⊗[K] E) :
      η.norm ω x = Real.sqrt (RCLike.re (c.inner x x)) := by
    exact ξ.withFibreNorm_norm ω p (innerProductCoreSeminorm_eq_zero_iff c) x
  have hs (x : (S.ϕ ω).Completion ⊗[K] E) :
      (η.norm ω x) ^ 2 = RCLike.re (c.inner x x) := by
    rw [hn]
    exact Real.sq_sqrt (c.re_inner_nonneg x)
  have hp := η.norm_completedDeterminantPairing_eq_of_innerProductCore ω c hs
    (1 ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E))
    (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E))
  rw [completedDeterminantGenerator_pairing, norm_one] at hp
  exact ξ.determinantDiscrepancy_le_pow_of_majorant η ω
    (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hr))
    (fun x ↦ by rw [hn]; exact (hc x).1)
    (fun x ↦ by rw [hn]; exact (hc x).2) hp.symm

/-- The logarithmic form of the sharp John bound, with the rank-zero
convention giving zero on both sides. -/
theorem log_determinantDiscrepancy_le_half_finrank_mul_log_finrank
    (ξ : NormFamily S E) (ω : S.Ω)
    [IsRCLikeNormedField (S.ϕ ω).Completion] :
    Real.log (ξ.determinantDiscrepancy ω) ≤
      (Module.finrank K E : ℝ) / 2 * Real.log (Module.finrank K E) := by
  calc
    Real.log (ξ.determinantDiscrepancy ω) ≤
        Real.log (Real.sqrt (Module.finrank K E) ^ Module.finrank K E) :=
      Real.log_le_log (ξ.determinantDiscrepancy_pos ω)
        (ξ.determinantDiscrepancy_le_sqrt_finrank_pow ω)
    _ = _ := by
      rw [Real.log_pow, Real.log_sqrt (Nat.cast_nonneg _)]
      ring

/-- Finite places contribute zero; the sharp logarithmic discrepancy is
bounded by the rank constant supported on the infinite locus. -/
theorem log_determinantDiscrepancy_le_indicator (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized] (ω : S.Ω) :
    Real.log (ξ.determinantDiscrepancy ω) ≤
      S.Ωinf.indicator (fun _ ↦
        (Module.finrank K E : ℝ) / 2 * Real.log (Module.finrank K E)) ω := by
  classical
  by_cases hω : ω ∈ S.Ωinf
  · let := hN ω hω
    rw [Set.indicator_of_mem hω]
    exact ξ.log_determinantDiscrepancy_le_half_finrank_mul_log_finrank ω
  · have hf : ω ∈ S.Ωfin := not_not.mp hω
    rw [Set.indicator_of_notMem hω, ξ.determinantDiscrepancy_eq_one_finite ω hf,
      Real.log_one]

/-- Inner-product norms only at infinity suffice for discrepancy one
everywhere; finite vector norms need no ultrametric hypothesis. -/
theorem determinantDiscrepancy_eq_one_of_archimedeanInnerProducts
    (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (hI : ∀ (ω : S.Ω) (hω : ω ∈ S.Ωinf),
      letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion (h := hN ω hω)
      ∃ c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E),
        ∀ x, (ξ.norm ω x) ^ 2 = RCLike.re (c.inner x x))
    (ω : S.Ω) : ξ.determinantDiscrepancy ω = 1 := by
  by_cases hω : ω ∈ S.Ωinf
  · let := hN ω hω
    obtain ⟨c, hc⟩ := hI ω hω
    exact ξ.determinantDiscrepancy_eq_one_of_innerProductCore ω c hc
  · exact ξ.determinantDiscrepancy_eq_one_finite ω (not_not.mp hω)

end NormFamily

namespace AdelicVectorBundle

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The sharp upper bound in Proposition4.3.10 follows by integrating the
actual local determinant discrepancy, in every rank. -/
theorem degree_add_degree_dual_le [S.IsProper] (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    V.degree + (V.dualOfMeasurableBase).degree ≤
      (Module.finrank K V : ℝ) / 2 * Real.log (Module.finrank K V) *
        (S.v S.Ωinf).toReal := by
  rw [V.degree_add_degree_dual_eq_integral_log_determinantDiscrepancy]
  let C := (Module.finrank K V : ℝ) / 2 * Real.log (Module.finrank K V)
  have hR : Integrable (S.Ωinf.indicator (fun _ ↦ C)) S.v :=
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr
      (integrableOn_const (S.v_Ωinf_lt_top_of_isRCLike).ne)
  calc
    (∫ ω, Real.log (V.toNormFamily.determinantDiscrepancy ω) ∂S.v) ≤
        ∫ ω, S.Ωinf.indicator (fun _ ↦ C) ω ∂S.v :=
      integral_mono (V.integrable_log_determinantDiscrepancy) hR
        (V.toNormFamily.log_determinantDiscrepancy_le_indicator)
    _ = _ := by
      rw [integral_indicator_const C S.measurableSet_Ωinf]
      change (S.v S.Ωinf).toReal * C = C * (S.v S.Ωinf).toReal
      ring

/-- The last clause of Proposition4.3.10 assumes inner products only at
infinity, allowing arbitrary finite-place vector norms. -/
theorem degree_add_degree_dual_eq_zero_of_archimedeanInnerProducts [S.IsProper]
    (V : AdelicVectorBundle S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    (hI : ∀ (ω : S.Ω) (hω : ω ∈ S.Ωinf),
      letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion (h := hN ω hω)
      ∃ c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] V),
        ∀ x, (V.toNormFamily.norm ω x) ^ 2 = RCLike.re (c.inner x x)) :
    V.degree + (V.dualOfMeasurableBase).degree = 0 := by
  rw [V.degree_add_degree_dual_eq_integral_log_determinantDiscrepancy]
  have he : (fun ω ↦ Real.log (V.toNormFamily.determinantDiscrepancy ω)) =
      (fun _ ↦ (0 : ℝ)) := by
    funext ω
    rw [V.toNormFamily.determinantDiscrepancy_eq_one_of_archimedeanInnerProducts hI ω,
      Real.log_one]
  rw [he, integral_zero]

end AdelicVectorBundle

end

end ArakelovGeometry

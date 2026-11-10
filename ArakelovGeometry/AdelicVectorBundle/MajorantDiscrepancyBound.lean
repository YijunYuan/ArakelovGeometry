/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.MajorantDiscrepancy
public import ArakelovGeometry.AdelicVectorBundle.StrongDomination

/-!
# Local majorant discrepancy bounds and domination

The actual majorant infimum is bounded using actual John cores at infinity
and scaled completed bidual norms at finite places. Strong domination then
provides integrable envelopes for its logarithm, as in Proposition4.3.11.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

/-- The logarithm of determinant discrepancy has integrable envelopes solely
from the sharp finite-support bound, without measurability of the family. -/
theorem log_determinantDiscrepancy_hasIntegrableBounds (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    HasIntegrableBounds (fun ω ↦ Real.log (ξ.determinantDiscrepancy ω)) S.v := by
  refine ⟨⟨S.Ωinf.indicator (fun _ ↦ (Module.finrank K E : ℝ) / 2 *
    Real.log (Module.finrank K E)), ?_,
    Filter.Eventually.of_forall (ξ.log_determinantDiscrepancy_le_indicator hN)⟩,
    ⟨0, integrable_zero _ _ _,
      Filter.Eventually.of_forall (ξ.log_determinantDiscrepancy_nonneg)⟩⟩
  exact (integrable_indicator_iff S.measurableSet_Ωinf).mpr
    (integrableOn_const (S.v_Ωinf_lt_top_of_isRCLike hN).ne)

/-- The local elementary condition gives the exact unit discrepancy used in
comparing the determinant discrepancy with each majorant ratio. -/
theorem IsElementaryAt.determinantDiscrepancy_eq_one {η : NormFamily S E}
    {hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion} {ω : S.Ω}
    (he : η.IsElementaryAt hN ω) : η.determinantDiscrepancy ω = 1 := by
  by_cases hω : ω ∈ S.Ωinf
  · let := hN ω hω
    obtain ⟨c, hc⟩ := he.2 hω
    exact η.determinantDiscrepancy_eq_one_of_innerProductCore ω c hc
  · exact η.determinantDiscrepancy_eq_one_finite ω (not_not.mp hω)

/-- Determinant order and dual antitonicity compare actual discrepancy with
every eligible actual majorant determinant ratio. -/
theorem determinantDiscrepancy_le_ratio_of_elementaryMajorant
    (ξ η : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω)
    (he : η.IsElementaryAt hN ω) (hl : ∀ x, ξ.norm ω x ≤ η.norm ω x) :
    ξ.determinantDiscrepancy ω ≤
      η.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) /
      ξ.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) := by
  let w := (1 : (S.ϕ ω).Completion) ⊗ₜ[K] determinantGenerator (K := K) (E := E)
  let z := (1 : (S.ϕ ω).Completion) ⊗ₜ[K] dualDeterminantGenerator (K := K) (E := E)
  have hp : η.determinant.norm ω w * η.dual.determinant.norm ω z = 1 := by
    have h := he.determinantDiscrepancy_eq_one
    change (η.determinant.norm ω w * η.dual.determinant.norm ω z)⁻¹ = 1 at h
    exact inv_eq_one.mp h
  have hd := η.dual.determinant_norm_mono ξ.dual ω
    (ξ.dual_norm_antitone η ω hl) z
  have hm := mul_le_mul_of_nonneg_left hd (η.determinant.norm_nonneg ω w)
  rw [hp] at hm
  have hw := ξ.determinant.norm_rational_pos ω determinantGenerator_ne_zero
  have hz := ξ.dual.determinant.norm_rational_pos ω dualDeterminantGenerator_ne_zero
  change (ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z)⁻¹ ≤
    η.determinant.norm ω w / ξ.determinant.norm ω w
  rw [← one_div, div_le_div_iff₀ (mul_pos hw hz) hw]
  have ht := mul_le_mul_of_nonneg_right hm hw.le
  nlinarith

/-- Taking the actual nonempty infimum gives the source comparison δ≤Δ. -/
theorem determinantDiscrepancy_le_majorantDiscrepancy (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) :
    ξ.determinantDiscrepancy ω ≤ ξ.majorantDiscrepancy hN ω := by
  by_cases hr : Module.finrank K E = 0
  · rw [ξ.determinantDiscrepancy_eq_one_of_finrank_eq_zero hr,
      ξ.majorantDiscrepancy_eq_one_of_finrank_eq_zero hN hr]
  · rw [majorantDiscrepancy, ite_eq_right hr]
    apply le_csInf (ξ.majorantRatios_nonempty hN ω)
    rintro a ⟨η, he, hl, rfl⟩
    exact ξ.determinantDiscrepancy_le_ratio_of_elementaryMajorant η hN ω he hl

/-- The actual John core gives the sharp majorant-discrepancy bound at every
normalized infinite place, including rank zero. -/
theorem majorantDiscrepancy_le_sqrt_finrank_pow (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    ξ.majorantDiscrepancy hN ω ≤
      Real.sqrt (Module.finrank K E) ^ Module.finrank K E := by
  by_cases hr : Module.finrank K E = 0
  · rw [ξ.majorantDiscrepancy_eq_one_of_finrank_eq_zero hN hr, hr, pow_zero]
  let := hN ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  obtain ⟨c, hc⟩ := ξ.exists_archimedean_john_innerProductCore ω
  let p := innerProductCoreSeminorm c
  let η := ξ.withFibreNorm ω p (innerProductCoreSeminorm_eq_zero_iff c)
  have hn (x : (S.ϕ ω).Completion ⊗[K] E) :
      η.norm ω x = Real.sqrt (RCLike.re (c.inner x x)) :=
    ξ.withFibreNorm_norm ω p _ x
  have he : η.IsElementaryAt hN ω := by
    refine ⟨fun hf ↦ False.elim (hω hf), fun _ ↦ ?_⟩
    exact ⟨c, fun x ↦ by rw [hn]; exact Real.sq_sqrt (c.re_inner_nonneg x)⟩
  have h := ξ.majorantDiscrepancy_le_ratio η hN ω he
    (fun x ↦ by rw [hn]; exact (hc x).1)
  apply h.trans
  apply (div_le_iff₀ (ξ.determinant.norm_rational_pos ω determinantGenerator_ne_zero)).mpr
  exact η.determinant_norm_le_mul_pow ξ ω
    (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hr))
    (fun x ↦ by rw [hn]; exact (hc x).2) _

/-- At a finite place, scaling the actual completed bidual norm by the
exponential distance provides an ultrametric majorant of the original norm.
Determinant bidual equality makes its ratio exactly the rank power. -/
theorem majorantDiscrepancy_le_exp_bidual_localDist_pow_finite (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    ξ.majorantDiscrepancy hN ω ≤
      Real.exp (ξ.localDist (ξ.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K)) ω) ^ Module.finrank K E := by
  let β := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
  let a : S.Ω → ℝ := fun _ ↦ Real.exp (ξ.localDist β ω)
  have ha : ∀ ω', 0 < a ω' := fun _ ↦ Real.exp_pos _
  let η := β.scale a ha
  have hu : η.IsUltrametric :=
    (ξ.dual.dual_isUltrametric.pullback _ _).scale a ha
  have he : η.IsElementaryAt hN ω :=
    ⟨hu ω, fun hi ↦ False.elim (hi hω)⟩
  have hl (x : (S.ϕ ω).Completion ⊗[K] E) : ξ.norm ω x ≤ η.norm ω x := by
    change ξ.norm ω x ≤ a ω * β.norm ω x
    simpa only [localDist_comm] using β.norm_le_exp_localDist_mul ξ ω x
  have h := ξ.majorantDiscrepancy_le_ratio η hN ω he hl
  have hd : β.determinant.norm ω
      (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) =
      ξ.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) :=
    congrArg (fun θ ↦ θ.norm ω
      (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)))
      (ξ.determinant_dual_dual_pullback hN)
  change ξ.majorantDiscrepancy hN ω ≤ (β.scale a ha).determinant.norm ω
    (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) /
      ξ.determinant.norm ω (1 ⊗ₜ[K] determinantGenerator (K := K) (E := E)) at h
  rw [β.determinant_scale_norm a ha, hd, mul_div_assoc,
    div_self (ξ.determinant.norm_rational_pos ω determinantGenerator_ne_zero).ne',
    mul_one] at h
  exact h

/-- The sharp logarithmic bound at infinity. -/
theorem log_majorantDiscrepancy_le_half_finrank_mul_log_finrank (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    Real.log (ξ.majorantDiscrepancy hN ω) ≤
      (Module.finrank K E : ℝ) / 2 * Real.log (Module.finrank K E) := by
  have h := Real.log_le_log (ξ.majorantDiscrepancy_pos hN ω)
    (ξ.majorantDiscrepancy_le_sqrt_finrank_pow hN ω hω)
  rw [Real.log_pow, Real.log_sqrt (Nat.cast_nonneg _)] at h
  convert h using 1; ring

/-- The finite-place logarithmic bound retains the necessary rank factor. -/
theorem log_majorantDiscrepancy_le_finrank_mul_bidual_localDist_finite
    (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    Real.log (ξ.majorantDiscrepancy hN ω) ≤ (Module.finrank K E : ℝ) *
      ξ.localDist (ξ.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K)) ω := by
  have h := Real.log_le_log (ξ.majorantDiscrepancy_pos hN ω)
    (ξ.majorantDiscrepancy_le_exp_bidual_localDist_pow_finite hN ω hω)
  simpa only [Real.log_pow, Real.log_exp] using h

/-- A source-corrected pointwise bound combining the two local majorants. -/
theorem log_majorantDiscrepancy_le_finrank_mul_bidual_localDist_add_indicator
    (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) :
    Real.log (ξ.majorantDiscrepancy hN ω) ≤ (Module.finrank K E : ℝ) *
      ξ.localDist (ξ.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K)) ω +
      S.Ωinf.indicator (fun _ ↦ (Module.finrank K E : ℝ) / 2 *
        Real.log (Module.finrank K E)) ω := by
  classical
  by_cases hω : ω ∈ S.Ωinf
  · rw [Set.indicator_of_mem hω]
    apply (ξ.log_majorantDiscrepancy_le_half_finrank_mul_log_finrank hN ω hω).trans
    have h := mul_nonneg (Nat.cast_nonneg (Module.finrank K E))
      (ξ.localDist_nonneg (ξ.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K)) ω)
    linarith
  · rw [Set.indicator_of_notMem hω, add_zero]
    exact ξ.log_majorantDiscrepancy_le_finrank_mul_bidual_localDist_finite hN ω
      (not_not.mp hω)

/-- Strong domination supplies actual integrable upper and lower envelopes
for the logarithm of the actual infimum; no measurability is assumed for Δ. -/
theorem IsStronglyDominated.log_majorantDiscrepancy_hasIntegrableBounds
    {ξ : NormFamily S E} (hξ : ξ.IsStronglyDominated)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    HasIntegrableBounds (fun ω ↦ Real.log (ξ.majorantDiscrepancy hN ω)) S.v := by
  obtain ⟨A, hA, hb⟩ := hξ.2.1
  let R := S.Ωinf.indicator (fun _ ↦ (Module.finrank K E : ℝ) / 2 *
    Real.log (Module.finrank K E))
  have hR : Integrable R S.v :=
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr
      (integrableOn_const (S.v_Ωinf_lt_top_of_isRCLike hN).ne)
  refine ⟨⟨fun ω ↦ (Module.finrank K E : ℝ) * A ω + R ω,
    (hA.const_mul _).add hR, ?_⟩,
    ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall ?_⟩⟩
  · filter_upwards [hb] with ω hω
    exact (ξ.log_majorantDiscrepancy_le_finrank_mul_bidual_localDist_add_indicator
      hN ω).trans (add_le_add
      (mul_le_mul_of_nonneg_left hω (Nat.cast_nonneg (Module.finrank K E))) le_rfl)
  · exact ξ.log_majorantDiscrepancy_nonneg hN

end NormFamily

namespace AdelicVectorBundle

/-- Proposition4.3.11 for the actual majorant discrepancy of a strongly
adelic bundle, including rank zero. -/
theorem IsStronglyAdelic.log_majorantDiscrepancy_hasIntegrableBounds
    {V : AdelicVectorBundle S E} (hV : V.IsStronglyAdelic)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    HasIntegrableBounds (fun ω ↦ Real.log (V.toNormFamily.majorantDiscrepancy hN ω)) S.v :=
  NormFamily.IsStronglyDominated.log_majorantDiscrepancy_hasIntegrableBounds hV hN

end AdelicVectorBundle

end

end ArakelovGeometry

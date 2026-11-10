/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Bidual
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.Basic
import ArakelovGeometry.AdelicVectorBundle.Dual.BidualQuotient
import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HN
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.AdelicVectorBundle.Slope.Finite
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Actual minimal slopes and bidual norms at a trivial place

The original norm need not be ultrametric. Actual quotient compatibility
preserves its true minimum, while the actual bidual is ultrametric.
Completed functional bounds use the genuine trivial completion on every vector.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

namespace NormFamily

open AdelicStructure

open Classical in
private theorem trivial_completed_scalar_norm_le_one
    (a : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion) : ‖a‖ ≤ 1 := by
  rw [norm_trivialCompletion K]
  by_cases ha : trivialCompletionAlgEquiv K a = 0
  · rw [ha, map_zero]
    exact zero_le_one
  · rw [AbsoluteValue.trivial_apply ha]

open Classical in
/-- A genuine lower bound for the original rational norm bounds every
completed functional's actual dual norm; no ultrametricity is required. -/
theorem dual_norm_le_inv_of_trivialSeminorm_ge
    (ξ : NormFamily (singleTrivialPlace K) E) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≠ 0 → c ≤ ξ.trivialSeminorm x)
    (z : ((singleTrivialPlace K).ϕ PUnit.unit).Completion ⊗[K] Module.Dual K E) :
    ξ.dual.norm PUnit.unit z ≤ c⁻¹ := by
  apply ξ.dual_norm_le PUnit.unit z (inv_nonneg.mpr hc.le)
  intro x
  by_cases hx : x = 0
  · simp only [hx, map_zero]
    change ‖(0 : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion)‖ ≤ c⁻¹ * 0
    rw [_root_.norm_zero, mul_zero]
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  change C ⊗[K] E at x
  have hn : trivialCompletedTensorEquiv K E x ≠ 0 :=
    (trivialCompletedTensorEquiv K E).map_eq_zero_iff.not.mpr hx
  have hl := h _ hn
  change c ≤ ξ.norm PUnit.unit ((trivialCompletedTensorEquiv K E).symm
    (trivialCompletedTensorEquiv K E x)) at hl
  rw [LinearEquiv.symm_apply_apply] at hl
  have hs := trivial_completed_scalar_norm_le_one
    (dualBaseChangeEquiv K C E z x)
  exact hs.trans (by
    have hm := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hc.le)
    simpa only [inv_mul_cancel₀ hc.ne'] using hm)

open Classical in
/-- The same original lower bound is retained by the actual bidual norm
on every nonzero rational vector, using a genuine separating functional. -/
theorem trivialSeminorm_bidual_ge_of_trivialSeminorm_ge
    (ξ : NormFamily (singleTrivialPlace K) E) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≠ 0 → c ≤ ξ.trivialSeminorm x) (x : E) (hx : x ≠ 0) :
    c ≤ (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).trivialSeminorm x := by
  have hex : ∃ ℓ : Module.Dual K E, ℓ x ≠ 0 := by
    by_contra! hn
    have he : Module.Dual.eval K E x = 0 := by
      ext ℓ
      exact hn ℓ
    apply hx
    apply Module.eval_apply_injective K
    simpa only [map_zero] using he
  obtain ⟨ℓ, hℓ⟩ := hex
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let q : Seminorm C (C ⊗[K] Module.Dual K E) := ξ.dual.norm PUnit.unit
  let qq : Seminorm C (C ⊗[K] Module.Dual K (Module.Dual K E)) :=
    ξ.dual.dual.norm PUnit.unit
  have he := ξ.dual.norm_dual_tmul_apply_tmul_le PUnit.unit (1 : C) (1 : C)
    (Module.Dual.eval K E x) ℓ
  change ‖(1 : C) * 1 * algebraMap K C (ℓ x)‖ ≤
    qq ((1 : C) ⊗ₜ[K] Module.Dual.eval K E x) * q ((1 : C) ⊗ₜ[K] ℓ) at he
  rw [one_mul, one_mul, norm_trivialCompletion K,
    trivialCompletionAlgEquiv_algebraMap, AbsoluteValue.trivial_apply hℓ] at he
  have hd := ξ.dual_norm_le_inv_of_trivialSeminorm_ge hc h ((1 : C) ⊗ₜ[K] ℓ)
  have hb : 1 ≤ qq ((1 : C) ⊗ₜ[K] Module.Dual.eval K E x) * c⁻¹ :=
    he.trans (mul_le_mul_of_nonneg_left hd (apply_nonneg qq _))
  have hl : c ≤ qq ((1 : C) ⊗ₜ[K] Module.Dual.eval K E x) := by
    have hm := (le_div_iff₀ hc).mp (show 1 ≤
      qq ((1 : C) ⊗ₜ[K] Module.Dual.eval K E x) / c from by
        simpa only [div_eq_mul_inv] using hb)
    simpa only [one_mul] using hm
  rw [trivialSeminorm_apply]
  change qq ((Module.Dual.eval K E).baseChange C ((1 : C) ⊗ₜ[K] x)) ≥ c
  rw [LinearMap.baseChange_tmul]
  exact hl

omit [FiniteDimensional K E] in
open Classical in
/-- Every nonzero vector in a rational line has the generator's actual
norm, by trivial homogeneity, even when the ambient norm is not ultrametric. -/
theorem trivialSeminorm_restrict_span_eq
    (ξ : NormFamily (singleTrivialPlace K) E) (x : E) (y : K ∙ x) (hy : y ≠ 0) :
    (ξ.restrict (K ∙ x)).trivialSeminorm y = ξ.trivialSeminorm x := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.property
  have hya : (y : E) ≠ 0 := fun hz ↦ hy (Subtype.ext hz)
  have hane : a ≠ 0 := by
    intro hz
    apply hya
    rw [← ha, hz, zero_smul]
  rw [trivialSeminorm_apply, trivialSeminorm_apply]
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let q : Seminorm C (C ⊗[K] E) := ξ.norm PUnit.unit
  change q ((K ∙ x).subtype.baseChange C ((1 : C) ⊗ₜ[K] y)) =
    q ((1 : C) ⊗ₜ[K] x)
  rw [LinearMap.baseChange_tmul]
  change q ((1 : C) ⊗ₜ[K] (y : E)) = q ((1 : C) ⊗ₜ[K] x)
  rw [← ha]
  have he := ξ.norm_rational_smul PUnit.unit a x
  change q ((1 : C) ⊗ₜ[K] (a • x)) =
    (AbsoluteValue.trivial : AbsoluteValue K ℝ) a * q ((1 : C) ⊗ₜ[K] x) at he
  rw [AbsoluteValue.trivial_apply hane, one_mul] at he
  exact he

end NormFamily

namespace AdelicVectorBundle

open AdelicStructure

variable (V : AdelicVectorBundle (singleTrivialPlace K) E)
  (hS : DiscreteMeasurableSpace (singleTrivialPlace K).Ω ∨
    (singleTrivialPlace K).HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ (singleTrivialPlace K).Ωinf,
    IsRCLikeNormedField ((singleTrivialPlace K).ϕ ω).Completion)

open Classical in
/-- The genuine ultrametric minimum is the largest level whose literal
ball contains every vector, including the infinite zero-rank convention. -/
theorem le_minimalSlope_iff_trivialSeminorm_le (hV : V.toNormFamily.IsUltrametric)
    (t : ℝ) :
    (t : EReal) ≤ V.minimalSlope hS hN ↔
      ∀ x, V.toNormFamily.trivialSeminorm x ≤ Real.exp (-t) := by
  rw [← V.generalHNFiltration_eq_top_iff hS hN t,
    V.generalHNFiltration_eq_trivialFiltration hS hN hV t]
  constructor
  · intro he x
    have hm : x ∈ V.toNormFamily.trivialFiltration hV t := by
      rw [he]
      exact Submodule.mem_top
    exact hm
  · intro h
    apply top_unique
    intro x _
    exact h x

open Classical in
/-- For an arbitrary original norm, its actual minimum is characterized
by the actual bidual ball, without assuming original ultrametricity. -/
theorem le_minimalSlope_iff_trivialSeminorm_bidual_le (t : ℝ) :
    (t : EReal) ≤ V.minimalSlope hS hN ↔
      ∀ x, (V.bidualOfMeasurableBase hS).toNormFamily.trivialSeminorm x ≤ Real.exp (-t) := by
  rw [← V.minimalSlope_bidualOfMeasurableBase hS hN]
  exact (V.bidualOfMeasurableBase hS).le_minimalSlope_iff_trivialSeminorm_le hS hN
    (V.toNormFamily.dual.dual_isUltrametric.pullback
      (Module.Dual.eval K E) (Module.eval_apply_injective K)) t

open Classical in
/-- A positive-rank actual constant bidual has equal ordinary, modified,
and minimal slopes for the original arbitrary norm. -/
theorem slopes_eq_neg_log_of_trivialSeminorm_bidual_eq_const
    {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≠ 0 → (V.bidualOfMeasurableBase hS).toNormFamily.trivialSeminorm x = c)
    (hr : 0 < Module.finrank K E) :
    V.slope hS hN = -Real.log c ∧ V.modifiedSlope hS hN = -Real.log c ∧
      V.minimalSlope hS hN = (-Real.log c : ℝ) := by
  have hm : V.minimalSlope hS hN = (-Real.log c : ℝ) := by
    rw [← V.minimalSlope_bidualOfMeasurableBase hS hN]
    exact (V.bidualOfMeasurableBase hS).minimalSlope_eq_neg_log_of_trivialSeminorm_eq_const
      hS hN hc h hr
  have hs : V.slope hS hN = -Real.log c := by
    change V.degree hS hN / (Module.finrank K E : ℝ) = _
    rw [← V.degree_bidualOfMeasurableBase hS hN]
    exact (V.bidualOfMeasurableBase hS).slope_eq_neg_log_of_trivialSeminorm_eq_const
      hS hN hc h hr
  have hl := V.minimalSlope_le_modifiedSlope hS hN hr
  have hu := V.modifiedSlope_le_slope hS hN
  rw [hm] at hl
  rw [hs] at hu
  have he : V.modifiedSlope hS hN = -Real.log c :=
    le_antisymm hu (EReal.coe_le_coe_iff.mp hl)
  exact ⟨hs, he, hm⟩

open Classical in
/-- Source4.3.61 with its necessary positive-rank scope: the original
arbitrary norm is semistable exactly when its actual bidual is constant. -/
theorem isSemistable_iff_exists_trivialSeminorm_bidual_eq_const
    (hr : 0 < Module.finrank K E) :
    V.IsSemistable hS hN ↔ ∃ c : ℝ, 0 < c ∧
      ∀ x, x ≠ 0 → (V.bidualOfMeasurableBase hS).toNormFamily.trivialSeminorm x = c := by
  constructor
  · intro hV
    obtain ⟨m, hm⟩ := V.exists_minimalSlope_eq_coe hS hN hr
    have hp : ∀ x, x ≠ 0 → Real.exp (-m) ≤ V.toNormFamily.trivialSeminorm x := by
      intro x hx
      have hpx : 0 < V.toNormFamily.trivialSeminorm x := by
        rw [NormFamily.trivialSeminorm_apply]
        exact V.toNormFamily.norm_rational_pos PUnit.unit hx
      have hline : ∀ y, y ≠ 0 →
          (V.restrictOfMeasurableBase (K ∙ x) hS).toNormFamily.trivialSeminorm y =
            V.toNormFamily.trivialSeminorm x := by
        intro y hy
        exact V.toNormFamily.trivialSeminorm_restrict_span_eq x y hy
      have hmin := (V.isSemistable_iff_minimalSlope_restrict_le hS hN hr).mp hV (K ∙ x)
        (Submodule.span_singleton_eq_bot.not.mpr hx)
      have hlr : 0 < Module.finrank K (K ∙ x) := by
        rw [finrank_span_singleton hx]
        exact zero_lt_one
      have hlm := minimalSlope_eq_neg_log_of_trivialSeminorm_eq_const
        (V.restrictOfMeasurableBase (K ∙ x) hS) hS hN hpx hline hlr
      rw [hlm, hm] at hmin
      have hlog := EReal.coe_le_coe_iff.mp hmin
      have he := Real.exp_le_exp.mpr
        (show -m ≤ Real.log (V.toNormFamily.trivialSeminorm x) from by linarith)
      rwa [Real.exp_log hpx] at he
    have hu := (V.le_minimalSlope_iff_trivialSeminorm_bidual_le hS hN m).mp hm.ge
    refine ⟨Real.exp (-m), Real.exp_pos _, fun x hx ↦ le_antisymm (hu x) ?_⟩
    exact V.toNormFamily.trivialSeminorm_bidual_ge_of_trivialSeminorm_ge
      (Real.exp_pos _) hp x hx
  · rintro ⟨c, hc, h⟩
    obtain ⟨_, hmod, hmin⟩ :=
      V.slopes_eq_neg_log_of_trivialSeminorm_bidual_eq_const hS hN hc h hr
    apply (V.isSemistable_iff_modifiedSlope_eq_minimalSlope hS hN hr).mpr
    rw [hmod, hmin]

end AdelicVectorBundle

end

end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldPurity
import ArakelovGeometry.AdelicVectorBundle.Dual

/-!
# Purity and norm attainment on actual completed duals

The discrete completed scalar value group forces operator norms to be
actual scalar values and makes every nonzero dual norm attained.
No domination, coherence or primal ultrametricity premise is needed.
-/

open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing CompletedUnitBallGauge

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E]
  [Module K E] [FiniteDimensional K E]

theorem IsPureAtFinitePlaces.dual_evaluation_ratio_mem_valueGroup
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] Module.Dual K E)
    (x : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E)
    (hx : dualBaseChangeEquiv K _ E z x ≠ 0) :
    ∃ a : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion,
      a ≠ 0 ∧ ‖dualBaseChangeEquiv K _ E z x‖ / ξ.norm ω x = ‖a‖ := by
  have hxn : x ≠ 0 := by
    intro h
    exact hx (by rw [h, map_zero])
  obtain ⟨a, ha, hn⟩ := hξ ω hω x hxn
  refine ⟨dualBaseChangeEquiv K _ E z x / a, div_ne_zero hx ha, ?_⟩
  rw [norm_div, hn]

theorem IsPureAtFinitePlaces.dual_norm_eq_uniformizer_zpow
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {z : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion ⊗[K] Module.Dual K E} (hz : z ≠ 0) :
    ∃ n : ℤ, ξ.dual.norm (normalizedPrimeParameter p) z =
      ‖algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedPrimeParameter p)).Completion (primeUniformizer p)‖ ^ n := by
  let ω := normalizedPrimeParameter p
  let π := algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion
    (primeUniformizer p)
  have hρ : 0 < ‖π‖ := primeUniformizer_norm_pos p
  have hρlt : ‖π‖ < 1 := primeUniformizer_norm_lt_one p
  obtain ⟨n, hlow, hupper, _⟩ := completedUnitBallGauge_rounding ξ.dual p hz
  refine ⟨n, le_antisymm hupper ?_⟩
  by_contra h
  have hs : ξ.dual.norm ω z < ‖π‖ ^ n := lt_of_not_ge h
  have hb : ξ.dual.norm ω z ≤ ‖π‖ ^ (n + 1) := by
    apply ξ.dual_norm_le ω z (zpow_pos hρ _).le
    intro x
    by_cases he : dualBaseChangeEquiv K _ E z x = 0
    · rw [he, _root_.norm_zero]
      exact mul_nonneg (zpow_pos hρ _).le (ξ.norm_nonneg ω x)
    · have hx : x ≠ 0 := by
        intro h
        exact he (by rw [h, map_zero])
      have hxp : 0 < ξ.norm ω x := ξ.norm_pos ω hx
      obtain ⟨a, ha, han⟩ := hξ.dual_evaluation_ratio_mem_valueGroup ω
        (normalizedPrimeParameter_mem_fin p) z x he
      obtain ⟨m, hm⟩ := completed_norm_eq_uniformizer_zpow p ha
      have hr : ‖π‖ ^ m ≤ ξ.dual.norm ω z := by
        rw [← hm, ← han]
        exact (div_le_iff₀ hxp).mpr (ξ.norm_dual_apply_le ω z x)
      have hmn : n + 1 ≤ m := by
        have := (zpow_lt_zpow_iff_right_of_lt_one₀ hρ hρlt).mp (hr.trans_lt hs)
        omega
      apply (div_le_iff₀ hxp).mp
      rw [han, hm]
      exact (zpow_le_zpow_iff_right_of_lt_one₀ hρ hρlt).mpr hmn
  exact (not_le_of_gt hlow) hb

theorem IsPureAtFinitePlaces.dual
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) : ξ.dual.IsPureAtFinitePlaces := by
  intro ω hω z hz
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  obtain ⟨n, hn⟩ := hξ.dual_norm_eq_uniformizer_zpow p hz
  let π := algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
    (normalizedPrimeParameter p)).Completion (primeUniformizer p)
  have hπ : π ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K _).injective).mpr (primeUniformizer_ne_zero p)
  exact ⟨π ^ n, zpow_ne_zero _ hπ, hn.trans (norm_zpow π n).symm⟩

theorem IsPureAtFinitePlaces.exists_dual_norm_attaining_vector
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    {z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] Module.Dual K E}
    (hz : z ≠ 0) :
    ∃ x : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E,
      x ≠ 0 ∧ ‖dualBaseChangeEquiv K _ E z x‖ = ξ.dual.norm ω z * ξ.norm ω x := by
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  let ω := normalizedPrimeParameter p
  let π := algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion
    (primeUniformizer p)
  have hρ : 0 < ‖π‖ := primeUniformizer_norm_pos p
  have hρlt : ‖π‖ < 1 := primeUniformizer_norm_lt_one p
  obtain ⟨n, hn⟩ := hξ.dual_norm_eq_uniformizer_zpow p hz
  have hex : ∃ x : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E,
      ‖π‖ ^ (n + 1) * ξ.norm ω x < ‖dualBaseChangeEquiv K _ E z x‖ := by
    by_contra! h
    have hb := ξ.dual_norm_le ω z (zpow_pos hρ (n + 1)).le h
    rw [hn] at hb
    have hl : ‖π‖ ^ (n + 1) < ‖π‖ ^ n :=
      (zpow_lt_zpow_iff_right_of_lt_one₀ hρ hρlt).mpr (by omega)
    exact (not_le_of_gt hl) hb
  obtain ⟨x, hxe⟩ := hex
  have hx : x ≠ 0 := by
    intro h
    rw [h, ξ.norm_zero, map_zero, _root_.norm_zero, mul_zero] at hxe
    exact (lt_irrefl 0) hxe
  have he : dualBaseChangeEquiv K _ E z x ≠ 0 := by
    intro h
    rw [h, _root_.norm_zero] at hxe
    exact (not_lt_of_ge (mul_nonneg (zpow_pos hρ _).le (ξ.norm_nonneg ω x))) hxe
  have hxp : 0 < ξ.norm ω x := ξ.norm_pos ω hx
  obtain ⟨a, ha, han⟩ := hξ.dual_evaluation_ratio_mem_valueGroup ω
    (normalizedPrimeParameter_mem_fin p) z x he
  obtain ⟨m, hm⟩ := completed_norm_eq_uniformizer_zpow p ha
  have hr : ‖π‖ ^ m ≤ ‖π‖ ^ n := by
    rw [← hm, ← han, ← hn]
    exact (div_le_iff₀ hxp).mpr (ξ.norm_dual_apply_le ω z x)
  have hl : ‖π‖ ^ (n + 1) < ‖π‖ ^ m := by
    rw [← hm, ← han]
    exact (lt_div_iff₀ hxp).mpr hxe
  have hmn : m = n := by
    have hnm := (zpow_le_zpow_iff_right_of_lt_one₀ hρ hρlt).mp hr
    have hmn := (zpow_lt_zpow_iff_right_of_lt_one₀ hρ hρlt).mp hl
    omega
  refine ⟨x, hx, (div_eq_iff hxp.ne').mp ?_⟩
  rw [han, hm, hmn, hn]

theorem globalImpurity_eq_zero_dual
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hσ : ξ.globalImpurity = 0) : ξ.dual.globalImpurity = 0 :=
  (ξ.isPureAtFinitePlaces_iff_globalImpurity_eq_zero.mpr hσ).dual.globalImpurity_eq_zero

end ArakelovGeometry.NormFamily

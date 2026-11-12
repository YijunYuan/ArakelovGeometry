/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Purity.Basic

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction

/-! # Actual pure finite-place quotient norms

The genuine quotient infimum is a completed scalar value and is attained.
This proves quotient purity without assuming an integral model or a lift
attainment certificate. Finite ultrametricity is required only for the
subsequent equality with the quotient's actual lattice gauge family.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing CompletedUnitBallGauge

variable {K E G : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup G] [Module K G]

theorem IsPureAtFinitePlaces.exists_pushforward_norm_eq_uniformizer_zpow
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (p : HeightOneSpectrum (𝓞 K))
    {z : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion ⊗[K] G} (hz : z ≠ 0) :
    ∃ n : ℤ, (ξ.pushforward π hπ).norm (normalizedPrimeParameter p) z =
      ‖algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedPrimeParameter p)).Completion (primeUniformizer p)‖ ^ n := by
  obtain ⟨n, hlow, hupper, _⟩ :=
    completedUnitBallGauge_rounding (ξ.pushforward π hπ) p hz
  refine ⟨n, le_antisymm hupper ?_⟩
  apply (ξ.le_quotientSeminorm_iff π hπ _ z _).mpr
  intro x hx
  have hx0 : x ≠ 0 := by
    intro he
    exact hz (by rw [← hx, he, map_zero])
  obtain ⟨a, ha, han⟩ := hξ _ (normalizedPrimeParameter_mem_fin p) x hx0
  obtain ⟨m, hm⟩ := completed_norm_eq_uniformizer_zpow p ha
  have hle := ξ.pushforward_norm_le π hπ (normalizedPrimeParameter p) x
  rw [hx, han, hm] at hle
  have hmn : m ≤ n := by
    have := (zpow_lt_zpow_iff_right_of_lt_one₀
      (primeUniformizer_norm_pos p) (primeUniformizer_norm_lt_one p)).mp
        (hlow.trans_le hle)
    omega
  rw [han, hm]
  exact (zpow_le_zpow_iff_right_of_lt_one₀
    (primeUniformizer_norm_pos p) (primeUniformizer_norm_lt_one p)).mpr hmn

theorem IsPureAtFinitePlaces.exists_pushforward_lift_norm_eq
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] G) :
    ∃ x, π.baseChange ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion x = z ∧
      ξ.norm ω x = (ξ.pushforward π hπ).norm ω z := by
  by_cases hz : z = 0
  · subst z
    exact ⟨0, map_zero _, by rw [ξ.norm_zero, (ξ.pushforward π hπ).norm_zero]⟩
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  obtain ⟨n, hn⟩ := hξ.exists_pushforward_norm_eq_uniformizer_zpow π hπ p hz
  let ρ := ‖algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
    (normalizedPrimeParameter p)).Completion (primeUniformizer p)‖
  have hgap : (ξ.pushforward π hπ).norm (normalizedPrimeParameter p) z < ρ ^ (n - 1) := by
    rw [hn]
    exact (zpow_lt_zpow_iff_right_of_lt_one₀
      (primeUniformizer_norm_pos p) (primeUniformizer_norm_lt_one p)).mpr (by omega)
  obtain ⟨x, hx, hlt⟩ := ξ.exists_pushforward_lift_lt π hπ (normalizedPrimeParameter p) z
    (sub_pos.mpr hgap)
  have hlt' : ξ.norm (normalizedPrimeParameter p) x < ρ ^ (n - 1) := by
    linarith
  have hx0 : x ≠ 0 := by
    intro he
    exact hz (by rw [← hx, he, map_zero])
  obtain ⟨a, ha, han⟩ := hξ _ (normalizedPrimeParameter_mem_fin p) x hx0
  obtain ⟨m, hm⟩ := completed_norm_eq_uniformizer_zpow p ha
  have hnm : n ≤ m := by
    rw [han, hm] at hlt'
    have := (zpow_lt_zpow_iff_right_of_lt_one₀
      (primeUniformizer_norm_pos p) (primeUniformizer_norm_lt_one p)).mp hlt'
    omega
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · rw [hn, han, hm]
    exact (zpow_le_zpow_iff_right_of_lt_one₀
      (primeUniformizer_norm_pos p) (primeUniformizer_norm_lt_one p)).mpr hnm
  · exact hx ▸ ξ.pushforward_norm_le π hπ (normalizedPrimeParameter p) x

theorem IsPureAtFinitePlaces.pushforward
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) (π : E →ₗ[K] G) (hπ : Function.Surjective π) :
    (ξ.pushforward π hπ).IsPureAtFinitePlaces := by
  constructor
  intro ω hω z hz
  obtain ⟨x, hx, hn⟩ := hξ.exists_pushforward_lift_norm_eq π hπ ω hω z
  have hx0 : x ≠ 0 := by
    intro he
    exact hz (by rw [← hx, he, map_zero])
  obtain ⟨a, ha, han⟩ := hξ ω hω x hx0
  exact ⟨a, ha, hn.symm.trans han⟩

theorem IsPureAtFinitePlaces.exists_quotient_lift_norm_eq
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) (F : Submodule K E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] (E ⧸ F)) :
    ∃ x, F.mkQ.baseChange ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion x = z ∧
      ξ.norm ω x = (ξ.quotient F).norm ω z :=
  hξ.exists_pushforward_lift_norm_eq F.mkQ F.mkQ_surjective ω hω z

theorem IsPureAtFinitePlaces.quotient
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) (F : Submodule K E) :
    (ξ.quotient F).IsPureAtFinitePlaces :=
  hξ.pushforward F.mkQ F.mkQ_surjective

theorem IsPureAtFinitePlaces.quotient_globalImpurity_eq_zero
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) (F : Submodule K E) :
    (ξ.quotient F).globalImpurity = 0 :=
  (ξ.quotient F).isPureAtFinitePlaces_iff_globalImpurity_eq_zero.mp (hξ.quotient F)

theorem IsPureAtFinitePlaces.quotient_latticeGaugeFamily_eq
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) (hU : ξ.IsUltrametric) (F : Submodule K E) :
    (ξ.quotient F).latticeGaugeFamily (hξ := (hU.quotient F)) = ξ.quotient F :=
  (hξ.quotient F).latticeGaugeFamily_eq (hU.quotient F)

instance instIsPureAtFinitePlacesPushforward
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsPureAtFinitePlaces]
    (π : E →ₗ[K] G) (hπ : Function.Surjective π) :
    (ξ.pushforward π hπ).IsPureAtFinitePlaces :=
  hξ.pushforward π hπ

instance instIsPureAtFinitePlacesQuotient
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsPureAtFinitePlaces]
    (P : Submodule K E) : (ξ.quotient P).IsPureAtFinitePlaces :=
  hξ.quotient P

end ArakelovGeometry.NormFamily

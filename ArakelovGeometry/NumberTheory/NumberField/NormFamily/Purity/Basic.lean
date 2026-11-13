/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Norm.Gauge
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Impurity.Basic

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction

/-!
# Finite-place purity on actual completed fibres

Purity is membership in the actual completed scalar value group.
On the normalized number-field curve this is equivalent to equality with
the intrinsic unit-ball gauge, and therefore to vanishing global impurity.
Injective pullbacks preserve the original completed norm values.
-/

@[expose] public section

open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

section AdelicCurve

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

/-- All nonzero completed finite-fibre norms lie in the value group of
the actual completed scalar field. -/
class IsPureAtFinitePlaces (ξ : NormFamily S E) : Prop where
  /-- The defining property. -/
  norm_mem_valueGroup :
    ∀ ω ∈ S.Ωfin, ∀ z : (S.ϕ ω).Completion ⊗[K] E, z ≠ 0 →
      ∃ a : (S.ϕ ω).Completion, a ≠ 0 ∧ ξ.norm ω z = ‖a‖

instance (ξ : NormFamily S E) : CoeFun (ξ.IsPureAtFinitePlaces)
    (fun _ ↦
      ∀ ω ∈ S.Ωfin, ∀ z : (S.ϕ ω).Completion ⊗[K] E, z ≠ 0 →
        ∃ a : (S.ϕ ω).Completion, a ≠ 0 ∧ ξ.norm ω z = ‖a‖) :=
  ⟨fun h ↦ h.norm_mem_valueGroup⟩

/-- The defining proposition of `IsPureAtFinitePlaces`. -/
theorem IsPureAtFinitePlaces.iff (ξ : NormFamily S E) :
    ξ.IsPureAtFinitePlaces ↔
    ∀ ω ∈ S.Ωfin, ∀ z : (S.ϕ ω).Completion ⊗[K] E, z ≠ 0 →
      ∃ a : (S.ϕ ω).Completion, a ≠ 0 ∧ ξ.norm ω z = ‖a‖ :=
  ⟨fun h ↦ h.norm_mem_valueGroup, fun h ↦ ⟨h⟩⟩

/-- An injective completed pullback retains each nonzero original norm value. -/
theorem IsPureAtFinitePlaces.pullback {ξ : NormFamily S E}
    (hξ : ξ.IsPureAtFinitePlaces) (f : F →ₗ[K] E) (hf : Function.Injective f) :
    (ξ.pullback f hf).IsPureAtFinitePlaces := by
  constructor
  intro ω hω z hz
  have hi : Function.Injective (f.baseChange (S.ϕ ω).Completion) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have him : f.baseChange (S.ϕ ω).Completion z ≠ 0 := by
    intro h
    exact hz (((f.baseChange (S.ϕ ω).Completion).map_eq_zero_iff hi).mp h)
  exact hξ ω hω _ him

/-- Restriction preserves finite-place purity, including the zero subspace. -/
theorem IsPureAtFinitePlaces.restrict {ξ : NormFamily S E}
    (hξ : ξ.IsPureAtFinitePlaces) (F : Submodule K E) :
    (ξ.restrict F).IsPureAtFinitePlaces :=
  hξ.pullback F.subtype F.subtype_injective

/-- A finite coordinate maximum is attained by an actual nonzero completed
scalar coordinate, including when the original basis may be empty. -/
instance ofBasis_isPureAtFinitePlaces {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K E) : (ofBasis S E b).IsPureAtFinitePlaces := by
  constructor
  classical
  intro ω _ z hz
  let c := (b.baseChange (S.ϕ ω).Completion).equivFun z
  have hp : 0 < ‖c‖ := (ofBasis S E b).norm_pos ω hz
  have hi : ∃ i, c i ≠ 0 := by
    by_contra! h
    have hc : c = 0 := funext h
    exact hp.ne' (hc ▸ _root_.norm_zero)
  obtain ⟨i, _⟩ := hi
  let : Nonempty ι := ⟨i⟩
  obtain ⟨j, hj⟩ := (IsGreatest.pi_norm c).1
  refine ⟨c j, ?_, hj.symm⟩
  intro h
  exact hp.ne' (hj.symm.trans (by simp [h]))

/-- The mixed basis family uses the same coordinate maximum at finite places. -/
instance ofBasisMixed_isPureAtFinitePlaces {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K E) : (ofBasisMixed S E b).IsPureAtFinitePlaces := by
  constructor
  intro ω hω z hz
  simpa only [ofBasisMixed_norm_of_finite b ω hω] using
    ofBasis_isPureAtFinitePlaces b ω hω z hz

instance instIsPureAtFinitePlacesPullback (ξ : NormFamily S E) [hξ : ξ.IsPureAtFinitePlaces]
    (f : F →ₗ[K] E) (hf : Function.Injective f) :
    (ξ.pullback f hf).IsPureAtFinitePlaces :=
  hξ.pullback f hf

instance instIsPureAtFinitePlacesRestrict (ξ : NormFamily S E) [hξ : ξ.IsPureAtFinitePlaces]
    (P : Submodule K E) : (ξ.restrict P).IsPureAtFinitePlaces :=
  hξ.restrict P

end AdelicCurve

section NumberField

open AdelicStructure ActualPrimeIndexing CompletedUnitBallGauge

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]

variable (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)

/-- Discrete rounding identifies purity with the literal intrinsic gauge
at each nonzero completed vector. -/
theorem completedUnitBallGauge_eq_norm_iff_norm_mem_valueGroup
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    {z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E}
    (hz : z ≠ 0) :
    completedUnitBallGauge ξ ω z = ξ.norm ω z ↔
      ∃ a : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion,
        a ≠ 0 ∧ ξ.norm ω z = ‖a‖ := by
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  constructor
  · intro heq
    obtain ⟨n, _, _, hn⟩ := completedUnitBallGauge_rounding ξ p hz
    let a := algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion (primeUniformizer p)
    have ha : a ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K _).injective).mpr (primeUniformizer_ne_zero p)
    refine ⟨a ^ n, zpow_ne_zero _ ha, ?_⟩
    rw [norm_zpow, ← heq]
    exact hn
  · rintro ⟨a, ha, hn⟩
    apply le_antisymm _ (completedUnitBallGauge_comparison ξ p z).1
    have hmem : a⁻¹ • z ∈ ξ.completedUnitBall (normalizedPrimeParameter p) := by
      change ξ.norm _ (a⁻¹ • z) ≤ 1
      rw [ξ.norm_smul, norm_inv, hn, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]
    exact (scalarLatticeGauge_le _ z ha hmem).trans_eq hn.symm

/-- The intrinsic value-group condition is equivalent to zero global impurity.
No domination, coherence or finite-dimensionality premise is used. -/
theorem isPureAtFinitePlaces_iff_globalImpurity_eq_zero :
    ξ.IsPureAtFinitePlaces ↔ ξ.globalImpurity = 0 := by
  rw [ξ.globalImpurity_eq_zero_iff]
  constructor
  · intro h ω hω z
    by_cases hz : z = 0
    · subst z
      let S := normalizedNumberFieldAdelicStructure K
      let := S.completedFinitePlaceNontriviallyNormedField ω hω
        (NormalizedNumberFieldPlaces.parameter_isNontrivial
          (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω))
      rw [completedUnitBallGauge, scalarLatticeGauge_zero _ (by
        change ξ.norm ω 0 ≤ 1
        simp), ξ.norm_zero]
    · exact (ξ.completedUnitBallGauge_eq_norm_iff_norm_mem_valueGroup ω hω hz).mpr
        (h ω hω z hz)
  · intro h
    constructor
    intro ω hω z hz
    exact (ξ.completedUnitBallGauge_eq_norm_iff_norm_mem_valueGroup ω hω hz).mp (h ω hω z)

theorem IsPureAtFinitePlaces.globalImpurity_eq_zero {ξ :
    NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) : ξ.globalImpurity = 0 :=
  ξ.isPureAtFinitePlaces_iff_globalImpurity_eq_zero.mp hξ

/-- A substantive restriction consumer of the actual value-group condition. -/
theorem globalImpurity_eq_zero_restrict (hσ : ξ.globalImpurity = 0)
    (F : Submodule K E) : (ξ.restrict F).globalImpurity = 0 :=
  ((ξ.isPureAtFinitePlaces_iff_globalImpurity_eq_zero.mpr hσ).restrict F).globalImpurity_eq_zero

variable [FiniteDimensional K E]

/-- The actual produced completed unit-ball gauge family is pure. -/
instance latticeGaugeFamily_isPureAtFinitePlaces [hξ : ξ.IsUltrametric] :
    (ξ.latticeGaugeFamily).IsPureAtFinitePlaces := by
  constructor
  intro ω hω z hz
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  obtain ⟨n, _, _, hn⟩ := completedUnitBallGauge_rounding ξ p hz
  let a := algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
    (normalizedPrimeParameter p)).Completion (primeUniformizer p)
  have ha : a ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K _).injective).mpr (primeUniformizer_ne_zero p)
  refine ⟨a ^ n, zpow_ne_zero _ ha, ?_⟩
  rw [ξ.latticeGaugeFamily_norm_finite _ (normalizedPrimeParameter_mem_fin p), norm_zpow]
  exact hn

/-- Pure finite norms are unchanged by lattice replacement; infinity is
retained by its original construction. -/
theorem IsPureAtFinitePlaces.latticeGaugeFamily_eq {ξ :
    NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces) (hu : ξ.IsUltrametric) :
    ξ.latticeGaugeFamily = ξ := by
  ext ω z
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · rw [ξ.latticeGaugeFamily_norm_finite ω hω]
    exact ξ.globalImpurity_eq_zero_iff.mp hξ.globalImpurity_eq_zero ω hω z
  · rw [ξ.latticeGaugeFamily_norm_not_finite ω hω]

end NumberField

end ArakelovGeometry.NormFamily

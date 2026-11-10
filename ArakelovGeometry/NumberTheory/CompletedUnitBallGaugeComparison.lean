/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.CompletedLatticeGauge
public import ArakelovGeometry.NumberTheory.NormFamilyNormalizedPrimeIndexing

/-!
# Intrinsic gauges of actual completed norm unit balls

Power bracketing supplies genuine admissible nonzero scalars. The comparison
uses the literal unit ball and the previously defined scalar-infimum gauge.
At actual normalized finite places the contracting scalar is produced from
an actual valuation-one uniformizer, rather than assumed from the comparison.
-/

@[expose] public section

open scoped NumberField TensorProduct WithZero

noncomputable section

namespace ArakelovGeometry.CompletedUnitBallGauge

section NormedSpace

variable {F X : Type*} [NontriviallyNormedField F] [NormedAddCommGroup X]
  [NormedSpace F X]

theorem inv_smul_mem_unitBall_iff (x : X) {a : F} (ha : a ≠ 0) :
    a⁻¹ • x ∈ {y : X | ‖y‖ ≤ 1} ↔ ‖x‖ ≤ ‖a‖ := by
  change ‖a⁻¹ • x‖ ≤ 1 ↔ _
  rw [norm_smul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr ha), mul_one]

/-- A power of a contracting scalar gives the strict upper rounding bound. -/
theorem exists_unitBall_scalar_lt (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1)
    {x : X} (hx : x ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ a⁻¹ • x ∈ {y : X | ‖y‖ ≤ 1} ∧
      ‖a‖ < ‖π‖⁻¹ * ‖x‖ := by
  have hρ : 0 < ‖π‖ := norm_pos_iff.mpr hπ
  have hy : 1 < ‖π‖⁻¹ := (one_lt_inv₀ hρ).mpr hπlt
  obtain ⟨n, hnlow, hnupper⟩ := exists_mem_Ioc_zpow (norm_pos_iff.mpr hx) hy
  let a : F := (π⁻¹) ^ (n + 1)
  have ha : a ≠ 0 := zpow_ne_zero _ (inv_ne_zero hπ)
  have han : ‖a‖ = (‖π‖⁻¹) ^ (n + 1) := by
    dsimp [a]
    rw [norm_zpow, norm_inv]
  refine ⟨a, ha, (inv_smul_mem_unitBall_iff x ha).mpr (by rwa [han]), ?_⟩
  rw [han, zpow_add₀ (ne_of_gt (inv_pos.mpr hρ)), zpow_one]
  simpa only [mul_comm] using mul_lt_mul_of_pos_right hnlow (inv_pos.mpr hρ)

theorem unitBall_gaugeValues_nonempty (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1)
    (x : X) : (scalarLatticeGaugeValues (F := F) {y : X | ‖y‖ ≤ 1} x).Nonempty := by
  by_cases hx : x = 0
  · subst x
    exact ⟨1, 1, one_ne_zero, by simp, norm_one⟩
  · obtain ⟨a, ha, hax, _⟩ := exists_unitBall_scalar_lt π hπ hπlt hx
    exact ⟨‖a‖, a, ha, hax, rfl⟩

theorem norm_le_unitBall_gauge (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1) (x : X) :
    ‖x‖ ≤ scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x := by
  apply le_csInf (unitBall_gaugeValues_nonempty π hπ hπlt x)
  rintro _ ⟨a, ha, hax, rfl⟩
  exact (inv_smul_mem_unitBall_iff x ha).mp hax

theorem unitBall_gauge_lt (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1)
    {x : X} (hx : x ≠ 0) :
    scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x < ‖π‖⁻¹ * ‖x‖ := by
  obtain ⟨a, ha, hax, halt⟩ := exists_unitBall_scalar_lt π hπ hπlt hx
  exact (scalarLatticeGauge_le _ x ha hax).trans_lt halt

theorem unitBall_gauge_le (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1) (x : X) :
    scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x ≤ ‖π‖⁻¹ * ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    rw [scalarLatticeGauge_zero _ (by simp), norm_zero, mul_zero]
  · exact (unitBall_gauge_lt π hπ hπlt hx).le

theorem unitBall_gauge_le_one_iff (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1) (x : X) :
    scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  constructor
  · exact fun hx => (norm_le_unitBall_gauge π hπ hπlt x).trans hx
  · intro hx
    simpa only [norm_one] using scalarLatticeGauge_le {y : X | ‖y‖ ≤ 1} x
      (one_ne_zero : (1 : F) ≠ 0) (by simpa using hx)

theorem unitBall_gauge_eq_zpow_of_bracket (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1)
    (hvalues : ∀ a : F, a ≠ 0 → ∃ m : ℤ, ‖a‖ = ‖π‖ ^ m)
    (x : X) (n : ℤ) (hlow : ‖π‖ ^ (n + 1) < ‖x‖) (hupper : ‖x‖ ≤ ‖π‖ ^ n) :
    scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x = ‖π‖ ^ n := by
  have hρ : 0 < ‖π‖ := norm_pos_iff.mpr hπ
  have ha : π ^ n ≠ 0 := zpow_ne_zero _ hπ
  have hax : (π ^ n)⁻¹ • x ∈ {y : X | ‖y‖ ≤ 1} :=
    (inv_smul_mem_unitBall_iff x ha).mpr (by simpa only [norm_zpow] using hupper)
  apply le_antisymm
  · simpa only [norm_zpow] using scalarLatticeGauge_le _ x ha hax
  · apply le_csInf (unitBall_gaugeValues_nonempty π hπ hπlt x)
    rintro _ ⟨c, hc, hcx, rfl⟩
    obtain ⟨m, hm⟩ := hvalues c hc
    have hcm : ‖x‖ ≤ ‖π‖ ^ m := by
      simpa only [hm] using (inv_smul_mem_unitBall_iff x hc).mp hcx
    have hmn : m ≤ n := by
      have := (zpow_lt_zpow_iff_right_of_lt_one₀ hρ hπlt).mp (hlow.trans_le hcm)
      omega
    rw [hm]
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hρ hπlt).mpr hmn

/-- Discreteness makes the intrinsic infimum the least scalar value above the norm. -/
theorem unitBall_gauge_discrete_rounding (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1)
    (hvalues : ∀ a : F, a ≠ 0 → ∃ m : ℤ, ‖a‖ = ‖π‖ ^ m) {x : X} (hx : x ≠ 0) :
    ∃ n : ℤ, ‖π‖ ^ (n + 1) < ‖x‖ ∧ ‖x‖ ≤ ‖π‖ ^ n ∧
      scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x = ‖π‖ ^ n := by
  obtain ⟨a, ha, hax, halt⟩ := exists_unitBall_scalar_lt π hπ hπlt hx
  obtain ⟨n, han⟩ := hvalues a ha
  have hupper : ‖x‖ ≤ ‖π‖ ^ n := by
    simpa only [han] using (inv_smul_mem_unitBall_iff x ha).mp hax
  have hlow : ‖π‖ ^ (n + 1) < ‖x‖ := by
    rw [zpow_add₀ (ne_of_gt (norm_pos_iff.mpr hπ)), zpow_one]
    simpa only [han, mul_comm] using (lt_inv_mul_iff₀ (norm_pos_iff.mpr hπ)).mp halt
  exact ⟨n, hlow, hupper,
    unitBall_gauge_eq_zpow_of_bracket π hπ hπlt hvalues x n hlow hupper⟩

end NormedSpace

section ActualFiniteCompletion

open NumberField IsDedekindDomain
open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]

/-- A genuine order-one scalar of the actual prime valuation. -/
def primeUniformizer (p : HeightOneSpectrum (𝓞 K)) : K :=
  (p.valuation_exists_uniformizer K).choose

theorem primeUniformizer_valuation (p : HeightOneSpectrum (𝓞 K)) :
    p.valuation K (primeUniformizer p) = WithZero.exp (-1 : ℤ) :=
  (p.valuation_exists_uniformizer K).choose_spec

theorem primeUniformizer_ne_zero (p : HeightOneSpectrum (𝓞 K)) :
    primeUniformizer p ≠ 0 := by
  intro h
  have hv := primeUniformizer_valuation p
  rw [h, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

theorem primeUniformizer_log_norm (p : HeightOneSpectrum (𝓞 K)) :
    Real.log ‖algebraMap K
      ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).Completion
      (primeUniformizer p)‖ = -normalizedPrimeLogScale p := by
  rw [(normalizedNumberFieldAdelicStructure K).norm_algebraMap_eq_absValue,
    normalizedPrime_log_value p (primeUniformizer_ne_zero p),
    primeUniformizer_valuation, WithZero.log_exp]
  push_cast
  ring

theorem primeUniformizer_norm_pos (p : HeightOneSpectrum (𝓞 K)) :
    0 < ‖algebraMap K
      ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).Completion
      (primeUniformizer p)‖ :=
  norm_pos_iff.mpr ((map_ne_zero_iff _ (algebraMap K _).injective).mpr
    (primeUniformizer_ne_zero p))

theorem primeUniformizer_norm_lt_one (p : HeightOneSpectrum (𝓞 K)) :
    ‖algebraMap K
      ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).Completion
      (primeUniformizer p)‖ < 1 := by
  apply (Real.log_neg_iff (primeUniformizer_norm_pos p)).mp
  rw [primeUniformizer_log_norm]
  exact neg_neg_of_pos (normalizedPrimeLogScale_pos p)

theorem rational_norm_eq_uniformizer_zpow (p : HeightOneSpectrum (𝓞 K))
    {a : K} (ha : a ≠ 0) :
    ‖algebraMap K
      ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).Completion a‖ =
      ‖algebraMap K
        ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).Completion
        (primeUniformizer p)‖ ^ (-(p.valuation K a).log) := by
  apply Real.log_injOn_pos
  · exact norm_pos_iff.mpr ((map_ne_zero_iff _ (algebraMap K _).injective).mpr ha)
  · exact zpow_pos (primeUniformizer_norm_pos p) _
  rw [Real.log_zpow, primeUniformizer_log_norm,
    (normalizedNumberFieldAdelicStructure K).norm_algebraMap_eq_absValue,
    normalizedPrime_log_value p ha]
  push_cast
  ring

/-- Density and ultrametricity show that completion adds no nonzero scalar norm values. -/
theorem exists_rational_same_completed_norm (p : HeightOneSpectrum (𝓞 K))
    {z : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion} (hz : z ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ‖algebraMap K
      ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).Completion a‖ =
      ‖z‖ := by
  let S := normalizedNumberFieldAdelicStructure K
  let ω := normalizedPrimeParameter p
  let := AbsoluteValue.isUltrametricDist_completion (S.ϕ ω)
    (normalizedPrimeParameter_mem_fin p)
  have hd : DenseRange (algebraMap K (S.ϕ ω).Completion) := by
    apply Dense.mono (hd := UniformSpace.Completion.denseRange_coe (α := WithAbs (S.ϕ ω)))
    rintro _ ⟨a, rfl⟩
    exact ⟨a.ofAbs, rfl⟩
  obtain ⟨a, ha⟩ := hd.exists_dist_lt z (norm_pos_iff.mpr hz)
  rw [dist_eq_norm] at ha
  have hab : ‖algebraMap K (S.ϕ ω).Completion a‖ ≤ ‖z‖ := by
    have hb := IsUltrametricDist.norm_add_le_max z (-(z - algebraMap K _ a))
    have he : z + -(z - algebraMap K (S.ϕ ω).Completion a) =
        algebraMap K (S.ϕ ω).Completion a := by abel
    rw [he, norm_neg, max_eq_left ha.le] at hb
    exact hb
  have hba : ‖z‖ ≤ ‖algebraMap K (S.ϕ ω).Completion a‖ := by
    by_contra h
    have h' := lt_of_not_ge h
    have hb := IsUltrametricDist.norm_add_le_max (z - algebraMap K _ a)
      (algebraMap K _ a)
    have hc := max_lt ha h'
    rw [sub_add_cancel] at hb
    exact (not_lt_of_ge hb) hc
  have heq := le_antisymm hab hba
  refine ⟨a, ?_, heq⟩
  intro ha0
  rw [ha0, map_zero, norm_zero] at heq
  exact (norm_pos_iff.mpr hz).ne' heq.symm

theorem completed_norm_eq_uniformizer_zpow (p : HeightOneSpectrum (𝓞 K))
    {z : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion} (hz : z ≠ 0) :
    ∃ n : ℤ, ‖z‖ = ‖algebraMap K
      ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).Completion
      (primeUniformizer p)‖ ^ n := by
  obtain ⟨a, ha, han⟩ := exists_rational_same_completed_norm p hz
  exact ⟨-(p.valuation K a).log, han.symm.trans (rational_norm_eq_uniformizer_zpow p ha)⟩

end ActualFiniteCompletion

section LocalImpurity

variable {F X : Type*} [NontriviallyNormedField F] [NormedAddCommGroup X]
  [NormedSpace F X]

/-- Literal logarithmic gauge ratios, with the zero vector excluded. -/
def unitBallGaugeLogValues : Set ℝ :=
  {r | ∃ x : X, x ≠ 0 ∧
    Real.log (scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x / ‖x‖) = r}

/-- The local impurity; the real supremum gives zero for a zero-dimensional space. -/
def unitBallGaugeImpurity : ℝ := sSup (unitBallGaugeLogValues (F := F) (X := X))

theorem unitBall_gauge_log_nonneg (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1)
    {x : X} (hx : x ≠ 0) :
    0 ≤ Real.log (scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x / ‖x‖) := by
  apply Real.log_nonneg
  exact (one_le_div (norm_pos_iff.mpr hx)).mpr (norm_le_unitBall_gauge π hπ hπlt x)

theorem unitBall_gauge_log_lt (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1)
    {x : X} (hx : x ≠ 0) :
    Real.log (scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x / ‖x‖) <
      -Real.log ‖π‖ := by
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hq := hp.trans_le (norm_le_unitBall_gauge π hπ hπlt x)
  have hratio := (div_lt_iff₀ hp).mpr (unitBall_gauge_lt π hπ hπlt hx)
  have hlog := Real.log_lt_log (div_pos hq hp) hratio
  rwa [Real.log_inv] at hlog

theorem unitBallGaugeLogValues_bddAbove (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1) :
    BddAbove (unitBallGaugeLogValues (F := F) (X := X)) := by
  refine ⟨-Real.log ‖π‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (unitBall_gauge_log_lt π hπ hπlt hx).le

theorem unitBallGaugeImpurity_nonneg (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1) :
    0 ≤ unitBallGaugeImpurity (F := F) (X := X) := by
  apply Real.sSup_nonneg
  rintro _ ⟨x, hx, rfl⟩
  exact unitBall_gauge_log_nonneg π hπ hπlt hx

theorem unitBallGaugeImpurity_le (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1) :
    unitBallGaugeImpurity (F := F) (X := X) ≤ -Real.log ‖π‖ := by
  apply Real.sSup_le
  · rintro _ ⟨x, hx, rfl⟩
    exact (unitBall_gauge_log_lt π hπ hπlt hx).le
  · exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg π) hπlt.le)

theorem unitBallGaugeImpurity_eq_zero_iff (π : F) (hπ : π ≠ 0) (hπlt : ‖π‖ < 1) :
    unitBallGaugeImpurity (F := F) (X := X) = 0 ↔
      ∀ x : X, scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x = ‖x‖ := by
  constructor
  · intro hδ x
    by_cases hx : x = 0
    · subst x
      simpa only [norm_zero] using scalarLatticeGauge_zero {y : X | ‖y‖ ≤ 1}
        (show (0 : X) ∈ {y : X | ‖y‖ ≤ 1} from by simp)
    · have hp := norm_pos_iff.mpr hx
      have hq := hp.trans_le (norm_le_unitBall_gauge π hπ hπlt x)
      have hle := le_csSup (unitBallGaugeLogValues_bddAbove (X := X) π hπ hπlt)
        (show Real.log (scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x / ‖x‖) ∈
          unitBallGaugeLogValues (F := F) (X := X) from ⟨x, hx, rfl⟩)
      change _ ≤ unitBallGaugeImpurity (F := F) (X := X) at hle
      rw [hδ] at hle
      have hlog := le_antisymm hle (unitBall_gauge_log_nonneg π hπ hπlt hx)
      have hratio : scalarLatticeGauge (F := F) {y : X | ‖y‖ ≤ 1} x / ‖x‖ = 1 := by
        apply Real.log_injOn_pos (div_pos hq hp)
          (show (1 : ℝ) ∈ Set.Ioi 0 from by norm_num)
        simpa only [Real.log_one] using hlog
      simpa only [one_mul] using (div_eq_iff (ne_of_gt hp)).mp hratio
  · intro heq
    apply le_antisymm _ (unitBallGaugeImpurity_nonneg π hπ hπlt)
    apply Real.sSup_le _ le_rfl
    rintro _ ⟨x, hx, rfl⟩
    rw [heq, div_self (ne_of_gt (norm_pos_iff.mpr hx)), Real.log_one]

theorem unitBallGaugeImpurity_subsingleton [Subsingleton X] :
    unitBallGaugeImpurity (F := F) (X := X) = 0 := by
  have hs : unitBallGaugeLogValues (F := F) (X := X) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨x, hx, _⟩
    exact hx (Subsingleton.elim x 0)
  unfold unitBallGaugeImpurity
  rw [hs, Real.sSup_empty]

end LocalImpurity

section ActualNormFamily

open NumberField IsDedekindDomain
open AdelicStructure ActualPrimeIndexing

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)

/-- The intrinsic gauge of the literal actual completed unit ball. -/
def completedUnitBallGauge (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E) : ℝ :=
  scalarLatticeGauge (F := ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion)
    (ξ.completedUnitBall ω) z

/-- The source's local logarithmic supremum on the actual completed fibre. -/
def completedUnitBallImpurity (ω : (normalizedNumberFieldAdelicStructure K).Ω) : ℝ :=
  sSup {r | ∃ z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E,
    z ≠ 0 ∧ Real.log (completedUnitBallGauge ξ ω z / ξ.norm ω z) = r}

theorem completedUnitBallGauge_rounding (p : HeightOneSpectrum (𝓞 K))
    {z : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion ⊗[K] E} (hz : z ≠ 0) :
    ∃ n : ℤ,
      ‖algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedPrimeParameter p)).Completion (primeUniformizer p)‖ ^ (n + 1) <
          ξ.norm (normalizedPrimeParameter p) z ∧
      ξ.norm (normalizedPrimeParameter p) z ≤
        ‖algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
          (normalizedPrimeParameter p)).Completion (primeUniformizer p)‖ ^ n ∧
      completedUnitBallGauge ξ (normalizedPrimeParameter p) z =
        ‖algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
          (normalizedPrimeParameter p)).Completion (primeUniformizer p)‖ ^ n := by
  let S := normalizedNumberFieldAdelicStructure K
  let ω := normalizedPrimeParameter p
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := S.completedFinitePlaceNontriviallyNormedField ω (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω))
  exact unitBall_gauge_discrete_rounding (algebraMap K (S.ϕ ω).Completion (primeUniformizer p))
    ((map_ne_zero_iff _ (algebraMap K _).injective).mpr (primeUniformizer_ne_zero p))
    (primeUniformizer_norm_lt_one p) (fun _ ha => completed_norm_eq_uniformizer_zpow p ha) hz

theorem completedUnitBallGauge_comparison (p : HeightOneSpectrum (𝓞 K))
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion ⊗[K] E) :
    ξ.norm (normalizedPrimeParameter p) z ≤
      completedUnitBallGauge ξ (normalizedPrimeParameter p) z ∧
      completedUnitBallGauge ξ (normalizedPrimeParameter p) z ≤
        ‖algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
          (normalizedPrimeParameter p)).Completion (primeUniformizer p)‖⁻¹ *
          ξ.norm (normalizedPrimeParameter p) z := by
  let S := normalizedNumberFieldAdelicStructure K
  let ω := normalizedPrimeParameter p
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := S.completedFinitePlaceNontriviallyNormedField ω (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω))
  have hπ := (map_ne_zero_iff _ (algebraMap K (S.ϕ ω).Completion).injective).mpr
    (primeUniformizer_ne_zero p)
  exact ⟨norm_le_unitBall_gauge _ hπ (primeUniformizer_norm_lt_one p) z,
    unitBall_gauge_le _ hπ (primeUniformizer_norm_lt_one p) z⟩

theorem completedUnitBallGauge_lt (p : HeightOneSpectrum (𝓞 K))
    {z : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion ⊗[K] E} (hz : z ≠ 0) :
    completedUnitBallGauge ξ (normalizedPrimeParameter p) z <
      ‖algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedPrimeParameter p)).Completion (primeUniformizer p)‖⁻¹ *
        ξ.norm (normalizedPrimeParameter p) z := by
  let S := normalizedNumberFieldAdelicStructure K
  let ω := normalizedPrimeParameter p
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := S.completedFinitePlaceNontriviallyNormedField ω (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω))
  exact unitBall_gauge_lt _
    ((map_ne_zero_iff _ (algebraMap K (S.ϕ ω).Completion).injective).mpr
      (primeUniformizer_ne_zero p)) (primeUniformizer_norm_lt_one p) hz

theorem completedUnitBallGauge_le_one_iff (p : HeightOneSpectrum (𝓞 K))
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ
      (normalizedPrimeParameter p)).Completion ⊗[K] E) :
    completedUnitBallGauge ξ (normalizedPrimeParameter p) z ≤ 1 ↔
      z ∈ ξ.completedUnitBall (normalizedPrimeParameter p) := by
  let S := normalizedNumberFieldAdelicStructure K
  let ω := normalizedPrimeParameter p
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := S.completedFinitePlaceNontriviallyNormedField ω (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω))
  exact unitBall_gauge_le_one_iff _
    ((map_ne_zero_iff _ (algebraMap K (S.ϕ ω).Completion).injective).mpr
      (primeUniformizer_ne_zero p)) (primeUniformizer_norm_lt_one p) z

theorem completedUnitBallImpurity_bounds (p : HeightOneSpectrum (𝓞 K)) :
    0 ≤ completedUnitBallImpurity ξ (normalizedPrimeParameter p) ∧
      completedUnitBallImpurity ξ (normalizedPrimeParameter p) ≤
        -Real.log ‖algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
          (normalizedPrimeParameter p)).Completion (primeUniformizer p)‖ := by
  let S := normalizedNumberFieldAdelicStructure K
  let ω := normalizedPrimeParameter p
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := S.completedFinitePlaceNontriviallyNormedField ω (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω))
  have hπ := (map_ne_zero_iff _ (algebraMap K (S.ϕ ω).Completion).injective).mpr
    (primeUniformizer_ne_zero p)
  exact ⟨unitBallGaugeImpurity_nonneg _ hπ (primeUniformizer_norm_lt_one p),
    unitBallGaugeImpurity_le _ hπ (primeUniformizer_norm_lt_one p)⟩

theorem completedUnitBallImpurity_eq_zero_iff (p : HeightOneSpectrum (𝓞 K)) :
    completedUnitBallImpurity ξ (normalizedPrimeParameter p) = 0 ↔
      ∀ z, completedUnitBallGauge ξ (normalizedPrimeParameter p) z =
        ξ.norm (normalizedPrimeParameter p) z := by
  let S := normalizedNumberFieldAdelicStructure K
  let ω := normalizedPrimeParameter p
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := S.completedFinitePlaceNontriviallyNormedField ω (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω))
  exact unitBallGaugeImpurity_eq_zero_iff _
    ((map_ne_zero_iff _ (algebraMap K (S.ϕ ω).Completion).injective).mpr
      (primeUniformizer_ne_zero p)) (primeUniformizer_norm_lt_one p)

theorem completedUnitBallImpurity_rank_zero [Subsingleton E]
    (p : HeightOneSpectrum (𝓞 K)) :
    completedUnitBallImpurity ξ (normalizedPrimeParameter p) = 0 := by
  apply (completedUnitBallImpurity_eq_zero_iff ξ p).mpr
  intro z
  have hz : z = 0 := Subsingleton.elim z 0
  subst z
  have hq := completedUnitBallGauge_comparison ξ p 0
  simp only [ξ.norm_zero, mul_zero] at hq ⊢
  exact le_antisymm hq.2 hq.1

end ActualNormFamily

end ArakelovGeometry.CompletedUnitBallGauge

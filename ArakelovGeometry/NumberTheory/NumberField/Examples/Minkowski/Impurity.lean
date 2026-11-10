/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Examples.Minkowski.Basic
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Impurity.Basic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.LocalDegree
import ArakelovGeometry.NumberTheory.NumberField.Examples.Minkowski.Determinant
import ArakelovGeometry.NumberTheory.NumberField.Examples.Minkowski.FiniteArithmetic
import Mathlib.Algebra.Order.Star.Real

/-! # Intrinsic completed impurity of the nonpure rational plane -/

@[expose] public section

open NumberField IsDedekindDomain
open MeasureTheory
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

open AdelicStructure ActualPrimeIndexing AdelicStructure.NormalizedNumberFieldPlaces
open NormFamily CompletedUnitBallGauge

theorem rational_prime_ramificationIdx (p : Nat.Primes) :
    (primeIdeal p).asIdeal.ramificationIdx ℤ = 1 := by
  have hef := normalizedPrime_localDegree_eq_ramificationIdx_mul_inertiaDeg (primeIdeal p)
  rw [rational_localDegree_one (A := DivisionRing.toRatAlgebra)] at hef
  have he := canonical_ramificationIdx_pos (primeIdeal p)
  have hle := Nat.le_mul_of_pos_right ((primeIdeal p).asIdeal.ramificationIdx ℤ)
    (canonical_inertiaDeg_pos (primeIdeal p))
  omega

theorem rational_primeLogScale (p : Nat.Primes) :
    normalizedPrimeLogScale (primeIdeal p) = Real.log (p.val : ℝ) := by
  let : (primeIdeal p).asIdeal.LiesOver (Ideal.span {(p.val : ℤ)}) :=
    normalizedPrimeParameter_liesOver_base (primeIdeal p) p (primePoint_base p)
  have hv := valuation_log_base_prime_eq_neg_ramificationIdx (primeIdeal p) p
  rw [rational_prime_ramificationIdx] at hv
  have h := normalizedPrime_log_value (primeIdeal p)
    (Nat.cast_ne_zero.mpr p.property.ne_zero : (p.val : ℚ) ≠ 0)
  change Real.log (S.ϕ (primePoint p) (p.val : ℚ)) = _ at h
  rw [rational_primeValue_prime, Real.log_inv, hv] at h
  norm_num at h
  linarith

theorem rational_completed_uniformizer_norm (p : Nat.Primes) :
    ‖algebraMap ℚ (S.ϕ (primePoint p)).Completion (primeUniformizer (primeIdeal p))‖ =
      (p.val : ℝ)⁻¹ := by
  apply Real.log_injOn_pos (primeUniformizer_norm_pos (primeIdeal p))
    (show (p.val : ℝ)⁻¹ ∈ Set.Ioi 0 from by
      change 0 < (p.val : ℝ)⁻¹
      exact inv_pos.mpr (by exact_mod_cast p.property.pos))
  rw [primeUniformizer_log_norm, rational_primeLogScale, Real.log_inv]

theorem rational_completed_scalar_norm (p : Nat.Primes)
    {c : (S.ϕ (primePoint p)).Completion} (hc : c ≠ 0) :
    ∃ m : ℤ, ‖c‖ = (p.val : ℝ)⁻¹ ^ m := by
  obtain ⟨m, hm⟩ := completed_norm_eq_uniformizer_zpow (primeIdeal p) hc
  change ‖c‖ = ‖algebraMap ℚ (S.ϕ (primePoint p)).Completion
    (primeUniformizer (primeIdeal p))‖ ^ m at hm
  exact ⟨m, by simpa only [rational_completed_uniformizer_norm] using hm⟩

theorem sqrt_prime_bounds (p : Nat.Primes) :
    1 < Real.sqrt (p.val : ℝ) ∧ Real.sqrt (p.val : ℝ) ≤ p.val := by
  have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hs : 1 < Real.sqrt (p.val : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hp
  refine ⟨hs, ?_⟩
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p.val)
  nlinarith [mul_nonneg (Real.sqrt_nonneg (p.val : ℝ)) (sub_nonneg.mpr hs.le)]

theorem family_prime_gauge_le_scalar (p : Nat.Primes) (a : ℤ)
    (z : (S.ϕ (primePoint p)).Completion ⊗[ℚ] Plane)
    {c : (S.ϕ (primePoint p)).Completion} (hc : c ≠ 0)
    (hzc : (family p a).norm (primePoint p) z ≤ ‖c‖) :
    completedUnitBallGauge (family p a) (primePoint p) z ≤ ‖c‖ := by
  apply scalarLatticeGauge_le ((family p a).completedUnitBall (primePoint p)) z hc
  change (family p a).norm (primePoint p) (c⁻¹ • z) ≤ 1
  rw [NormFamily.norm_smul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr hc), mul_one]
  exact hzc

theorem family_prime_gauge_le_sqrt_mul_norm (p : Nat.Primes) (a : ℤ)
    (z : (S.ϕ (primePoint p)).Completion ⊗[ℚ] Plane) :
    completedUnitBallGauge (family p a) (primePoint p) z ≤
      Real.sqrt (p.val : ℝ) * (family p a).norm (primePoint p) z := by
  by_cases hz : z = 0
  · subst z
    change completedUnitBallGauge (family p a) (normalizedPrimeParameter (primeIdeal p)) 0 ≤
      Real.sqrt (p.val : ℝ) * (family p a).norm (normalizedPrimeParameter (primeIdeal p)) 0
    rw [(family p a).norm_zero, mul_zero]
    simpa only [NormFamily.norm_zero, mul_zero] using
      (completedUnitBallGauge_comparison (family p a) (primeIdeal p) 0).2
  have hN : 0 < (family p a).norm (primePoint p) z :=
    lt_of_le_of_ne ((family p a).norm_nonneg _ _) (by
      exact Ne.symm (fun h => hz (((family p a).norm_eq_zero_iff _ _).mp h)))
  let u := firstCoordinate (primePoint p) z
  let w := shearedCoordinate a (primePoint p) z
  have hformula : (family p a).norm (primePoint p) z =
      max ‖u‖ (Real.sqrt (p.val : ℝ) * ‖w‖) := by
    rw [family_norm_prime]
    rfl
  by_cases hdom : Real.sqrt (p.val : ℝ) * ‖w‖ ≤ ‖u‖
  · have he : (family p a).norm (primePoint p) z = ‖u‖ :=
      hformula.trans (max_eq_left hdom)
    have hu : u ≠ 0 := norm_pos_iff.mp (by rwa [← he])
    exact (family_prime_gauge_le_scalar p a z hu he.le).trans (by
      rw [he]
      exact le_mul_of_one_le_left (norm_nonneg u) (sqrt_prime_bounds p).1.le)
  · have he : (family p a).norm (primePoint p) z = Real.sqrt (p.val : ℝ) * ‖w‖ :=
      hformula.trans (max_eq_right (le_of_not_ge hdom))
    have hw : w ≠ 0 := by
      intro hw
      rw [he, hw, _root_.norm_zero, mul_zero] at hN
      exact lt_irrefl _ hN
    let c : (S.ϕ (primePoint p)).Completion :=
      (algebraMap ℚ (S.ϕ (primePoint p)).Completion (p.val : ℚ))⁻¹ * w
    have hcNorm : ‖c‖ = (p.val : ℝ) * ‖w‖ := by
      dsimp only [c]
      rw [norm_mul, norm_inv, S.norm_algebraMap_eq_absValue,
        rational_primeValue_prime, inv_inv]
    have hc : c ≠ 0 := norm_pos_iff.mp (by
      rw [hcNorm]
      exact mul_pos (by exact_mod_cast p.property.pos) (norm_pos_iff.mpr hw))
    apply (family_prime_gauge_le_scalar p a z hc ?_).trans
    · rw [hcNorm, he, ← mul_assoc, ← pow_two, Real.sq_sqrt (by positivity)]
    · rw [hcNorm, he]
      exact mul_le_mul_of_nonneg_right (sqrt_prime_bounds p).2 (norm_nonneg w)

theorem family_prime_axis_one_gauge (p : Nat.Primes) (a : ℤ) :
    completedUnitBallGauge (family p a) (primePoint p)
      (1 ⊗ₜ[ℚ] (![0, 1] : Plane)) = p.val := by
  let ξ := family p a
  let ω := primePoint p
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := S.completedFinitePlaceNontriviallyNormedField ω (primePoint_mem_fin p)
    (parameter_isNontrivial (parameterMeasurableEquivNontrivialPlace.symm ω))
  let π := algebraMap ℚ (S.ϕ ω).Completion (primeUniformizer (primeIdeal p))
  have hπ : π ≠ 0 := (map_ne_zero_iff _ (algebraMap ℚ _).injective).mpr
    (primeUniformizer_ne_zero (primeIdeal p))
  have hπNorm : ‖π‖ = (p.val : ℝ)⁻¹ := rational_completed_uniformizer_norm p
  have hπlt : ‖π‖ < 1 := by
    rw [hπNorm]
    exact (inv_lt_one₀ (by exact_mod_cast p.property.pos)).mpr
      (by exact_mod_cast p.property.one_lt)
  have hN : ‖((1 : (S.ϕ ω).Completion) ⊗ₜ[ℚ] (![0, 1] : Plane))‖ = Real.sqrt (p.val : ℝ) :=
    family_norm_prime_axis_one p a
  have hlo : ‖π‖ ^ ((-1 : ℤ) + 1) < ‖((1 : (S.ϕ ω).Completion) ⊗ₜ[ℚ] (![0, 1] : Plane))‖ := by
    simpa only [neg_add_cancel, zpow_zero, hN] using (sqrt_prime_bounds p).1
  have hhi : ‖((1 : (S.ϕ ω).Completion) ⊗ₜ[ℚ] (![0, 1] : Plane))‖ ≤ ‖π‖ ^ (-1 : ℤ) := by
    simpa only [hN, hπNorm, zpow_neg_one, inv_inv] using (sqrt_prime_bounds p).2
  have h := unitBall_gauge_eq_zpow_of_bracket π hπ hπlt
    (fun c hc => completed_norm_eq_uniformizer_zpow (primeIdeal p) hc)
    (1 ⊗ₜ[ℚ] (![0, 1] : Plane)) (-1) hlo hhi
  change completedUnitBallGauge ξ ω (1 ⊗ₜ[ℚ] (![0, 1] : Plane)) = ‖π‖ ^ (-1 : ℤ) at h
  simpa only [hπNorm, zpow_neg_one, inv_inv] using h

theorem family_prime_log_gauge_ratio_le (p : Nat.Primes) (a : ℤ)
    {z : (S.ϕ (primePoint p)).Completion ⊗[ℚ] Plane} (hz : z ≠ 0) :
    Real.log (completedUnitBallGauge (family p a) (primePoint p) z /
      (family p a).norm (primePoint p) z) ≤ Real.log (p.val : ℝ) / 2 := by
  have hN : 0 < (family p a).norm (primePoint p) z :=
    lt_of_le_of_ne ((family p a).norm_nonneg _ _) (by
      exact Ne.symm (fun h => hz (((family p a).norm_eq_zero_iff _ _).mp h)))
  have hG : 0 < completedUnitBallGauge (family p a) (primePoint p) z :=
    hN.trans_le (completedUnitBallGauge_comparison (family p a) (primeIdeal p) z).1
  have hratio := (div_le_iff₀ hN).mpr (family_prime_gauge_le_sqrt_mul_norm p a z)
  have h := Real.log_le_log (div_pos hG hN) hratio
  rwa [Real.log_sqrt (by positivity)] at h

theorem family_prime_axis_one_log_gauge_ratio (p : Nat.Primes) (a : ℤ) :
    Real.log (completedUnitBallGauge (family p a) (primePoint p)
      (1 ⊗ₜ[ℚ] (![0, 1] : Plane)) /
      (family p a).norm (primePoint p) (1 ⊗ₜ[ℚ] (![0, 1] : Plane))) =
      Real.log (p.val : ℝ) / 2 := by
  rw [family_prime_axis_one_gauge, family_norm_prime_axis_one]
  have hp : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
  rw [Real.log_div hp.ne' (Real.sqrt_pos.mpr hp).ne', Real.log_sqrt hp.le]
  ring

theorem family_completedUnitBallImpurity_prime (p : Nat.Primes) (a : ℤ) :
    completedUnitBallImpurity (family p a) (primePoint p) = Real.log (p.val : ℝ) / 2 := by
  have hup : ∀ r ∈ {r | ∃ z : (S.ϕ (primePoint p)).Completion ⊗[ℚ] Plane,
      z ≠ 0 ∧ Real.log (completedUnitBallGauge (family p a) (primePoint p) z /
        (family p a).norm (primePoint p) z) = r}, r ≤ Real.log (p.val : ℝ) / 2 := by
    rintro _ ⟨z, hz, rfl⟩
    exact family_prime_log_gauge_ratio_le p a hz
  apply le_antisymm
  · exact Real.sSup_le hup (div_nonneg
      (Real.log_nonneg (by exact_mod_cast p.property.one_le)) (by norm_num))
  · apply le_csSup ⟨_, hup⟩
    refine ⟨1 ⊗ₜ[ℚ] (![0, 1] : Plane), ?_, family_prime_axis_one_log_gauge_ratio p a⟩
    intro hz
    have hn := family_norm_prime_axis_one p a
    rw [hz, NormFamily.norm_zero] at hn
    exact (Real.sqrt_pos.mpr (by exact_mod_cast p.property.pos)).ne' hn.symm

theorem family_completedUnitBallGauge_off_prime (p : Nat.Primes) (a : ℤ)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) (hne : ω ≠ primePoint p)
    (z : (S.ϕ ω).Completion ⊗[ℚ] Plane) :
    completedUnitBallGauge (family p a) ω z = (family p a).norm ω z := by
  have hn (w : (S.ϕ ω).Completion ⊗[ℚ] Plane) :
      (family p a).norm ω w = (ofBasis S Plane standardBasis).norm ω w := by
    rw [family_norm_off_prime p a ω hne, ofBasisHermitian_norm_of_finite standardBasis ω hω]
  have hball : (family p a).completedUnitBall ω =
      (completedBasisLattice S standardBasis ω hω : Set _) := by
    ext w
    change (family p a).norm ω w ≤ 1 ↔ w ∈ completedBasisLattice S standardBasis ω hω
    rw [hn, ofBasis_norm]
    exact (mem_basisCoordinateLattice_iff_norm_le_one (S.completedLocalRing ω hω)
      (S.mem_completedLocalRing ω hω) (standardBasis.baseChange (S.ϕ ω).Completion) w).symm
  unfold completedUnitBallGauge
  rw [hball, scalarLatticeGauge_completedBasisLattice standardBasis ω hω
    (parameter_isNontrivial (parameterMeasurableEquivNontrivialPlace.symm ω))]
  exact (hn z).symm

theorem family_completedUnitBallImpurity_off_prime (p : Nat.Primes) (a : ℤ)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) (hne : ω ≠ primePoint p) :
    completedUnitBallImpurity (family p a) ω = 0 := by
  obtain ⟨P, hP⟩ := exists_normalizedPrimeParameter_eq ω hω
  subst ω
  exact (completedUnitBallImpurity_eq_zero_iff (family p a) P).mpr
    (family_completedUnitBallGauge_off_prime p a _ hω hne)

theorem family_finiteImpurityProfile (p : Nat.Primes) (a : ℤ) :
    (family p a).finiteImpurityProfile =
      ({primePoint p} : Set S.Ω).indicator (fun _ => Real.log (p.val : ℝ) / 2) := by
  classical
  funext ω
  by_cases he : ω = primePoint p
  · subst ω
    rw [finiteImpurityProfile, ite_eq_left (primePoint_mem_fin p),
      family_completedUnitBallImpurity_prime]
    exact (Set.indicator_of_mem (Set.mem_singleton (primePoint p))
      (fun _ : S.Ω => Real.log (p.val : ℝ) / 2)).symm
  · have hne : ω ∉ ({primePoint p} : Set S.Ω) := by simpa only [Set.mem_singleton_iff] using he
    rw [Set.indicator_of_notMem hne]
    by_cases hω : ω ∈ S.Ωfin
    · rw [finiteImpurityProfile, ite_eq_left hω,
        family_completedUnitBallImpurity_off_prime p a ω hω he]
    · rw [finiteImpurityProfile, ite_eq_right hω]

theorem family_globalImpurity (p : Nat.Primes) (a : ℤ) :
    (family p a).globalImpurity = ENNReal.ofReal (Real.log (p.val : ℝ) / 2) := by
  classical
  let : DiscreteMeasurableSpace S.Ω := inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})
  rw [NormFamily.globalImpurity_eq_lintegral, family_finiteImpurityProfile]
  have hf : (fun ω : S.Ω => ENNReal.ofReal
      (({primePoint p} : Set S.Ω).indicator (fun _ => Real.log (p.val : ℝ) / 2) ω)) =
      ({primePoint p} : Set S.Ω).indicator
        (fun _ => ENNReal.ofReal (Real.log (p.val : ℝ) / 2)) := by
    funext ω
    by_cases hω : ω ∈ ({primePoint p} : Set S.Ω)
    · simp only [Set.indicator_of_mem hω]
    · simp only [Set.indicator_of_notMem hω, ENNReal.ofReal_zero]
  rw [hf, lintegral_indicator_const (measurableSet_singleton _), rational_singleton_mass, mul_one]

theorem family_globalImpurity_pos (p : Nat.Primes) (a : ℤ) :
    0 < (family p a).globalImpurity := by
  rw [family_globalImpurity, ENNReal.ofReal_pos]
  exact div_pos (Real.log_pos (by exact_mod_cast p.property.one_lt)) (by norm_num)

theorem family_not_pure (p : Nat.Primes) (a : ℤ) :
    ¬ ∀ ω ∈ S.Ωfin, ∀ z : (S.ϕ ω).Completion ⊗[ℚ] Plane,
      completedUnitBallGauge (family p a) ω z = (family p a).norm ω z := by
  intro h
  have hzero := ((family p a).globalImpurity_eq_zero_iff).mpr h
  exact (family_globalImpurity_pos p a).ne' hzero

theorem sqrt_prime_not_completed_scalar_norm (p : Nat.Primes)
    (c : (S.ϕ (primePoint p)).Completion) (hc : c ≠ 0) :
    ‖c‖ ≠ Real.sqrt (p.val : ℝ) := by
  intro he
  obtain ⟨m, hm⟩ := rational_completed_scalar_norm p hc
  have hlog := congrArg Real.log (hm.symm.trans he)
  rw [Real.log_zpow, Real.log_inv, Real.log_sqrt (by positivity)] at hlog
  have hp : 0 < Real.log (p.val : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hre : (2 : ℝ) * m = -1 := by nlinarith
  have hi : (2 : ℤ) * m = -1 := by exact_mod_cast hre
  omega

end ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

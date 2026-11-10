/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NonpureNumberFieldMinkowskiObstructionImpurity
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldPurity

/-! # Actual separation of the nonpure rational plane from all pure families -/

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

open AdelicStructure NormFamily CompletedUnitBallGauge

theorem family_not_isPureAtFinitePlaces (p : Nat.Primes) (a : ℤ) :
    ¬ (family p a).IsPureAtFinitePlaces := by
  intro h
  exact (family_globalImpurity_pos p a).ne'
    (((family p a).isPureAtFinitePlaces_iff_globalImpurity_eq_zero).mp h)

theorem integer_half_abs_ge (m : ℤ) : (1 / 2 : ℝ) ≤ |(m : ℝ) + 1 / 2| := by
  by_cases hm : 0 ≤ m
  · have hr : (0 : ℝ) ≤ m := by exact_mod_cast hm
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hm1 : m ≤ -1 := by omega
    have hr : (m : ℝ) ≤ -1 := by exact_mod_cast hm1
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem family_localDist_ge_of_pure (p : Nat.Primes) (a : ℤ)
    (η : NormFamily S Plane) (hη : η.IsPureAtFinitePlaces) :
    Real.log (p.val : ℝ) / 2 ≤ (family p a).localDist η (primePoint p) := by
  let z : (S.ϕ (primePoint p)).Completion ⊗[ℚ] Plane := 1 ⊗ₜ[ℚ] (![0, 1] : Plane)
  have hz : z ≠ 0 := by
    intro hz
    have hn := family_norm_prime_axis_one p a
    change (family p a).norm (primePoint p) z = _ at hn
    rw [hz, NormFamily.norm_zero] at hn
    exact (Real.sqrt_pos.mpr (by exact_mod_cast p.property.pos)).ne' hn.symm
  obtain ⟨c, hc, hnorm⟩ := hη (primePoint p) (primePoint_mem_fin p) z hz
  obtain ⟨m, hm⟩ := rational_completed_scalar_norm p hc
  have hηlog : Real.log (η.norm (primePoint p) z) = -(m : ℝ) * Real.log (p.val : ℝ) := by
    rw [hnorm, hm, Real.log_zpow, Real.log_inv]
    ring
  have hlogp : 0 ≤ Real.log (p.val : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.property.one_le)
  have hsub : Real.log ((family p a).norm (primePoint p) z) -
      Real.log (η.norm (primePoint p) z) = ((m : ℝ) + 1 / 2) * Real.log (p.val : ℝ) := by
    rw [hηlog, family_norm_prime_axis_one, Real.log_sqrt (by positivity)]
    ring
  have hd := (family p a).log_norm_sub_le_localDist η (primePoint p) z
  rw [hsub, abs_mul, abs_of_nonneg hlogp] at hd
  calc
    Real.log (p.val : ℝ) / 2 = (1 / 2 : ℝ) * Real.log (p.val : ℝ) := by ring
    _ ≤ |(m : ℝ) + 1 / 2| * Real.log (p.val : ℝ) :=
      mul_le_mul_of_nonneg_right (integer_half_abs_ge m) hlogp
    _ ≤ (family p a).localDist η (primePoint p) := hd

theorem family_lintegral_localDist_ge_of_pure (p : Nat.Primes) (a : ℤ)
    (η : NormFamily S Plane) (hη : η.IsPureAtFinitePlaces) :
    ENNReal.ofReal (Real.log (p.val : ℝ) / 2) ≤
      ∫⁻ ω, ENNReal.ofReal ((family p a).localDist η ω) ∂S.v := by
  classical
  let : DiscreteMeasurableSpace S.Ω := inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})
  have hf : ({primePoint p} : Set S.Ω).indicator
      (fun _ => ENNReal.ofReal (Real.log (p.val : ℝ) / 2)) ≤
      (fun ω => ENNReal.ofReal ((family p a).localDist η ω)) := by
    intro ω
    by_cases he : ω ∈ ({primePoint p} : Set S.Ω)
    · have hω : ω = primePoint p := he
      subst ω
      rw [Set.indicator_of_mem (Set.mem_singleton (primePoint p))]
      exact ENNReal.ofReal_le_ofReal (family_localDist_ge_of_pure p a η hη)
    · rw [Set.indicator_of_notMem he]
      exact zero_le
  have hi := lintegral_mono (μ := S.v) hf
  rw [lintegral_indicator_const (measurableSet_singleton _), rational_singleton_mass, mul_one] at hi
  exact hi

theorem family_integral_localDist_ge_of_pure (p : Nat.Primes) (a : ℤ)
    (η : NormFamily S Plane) (hη : η.IsPureAtFinitePlaces)
    (hI : Integrable ((family p a).localDist η) S.v) :
    Real.log (p.val : ℝ) / 2 ≤ ∫ ω, (family p a).localDist η ω ∂S.v := by
  have hn : 0 ≤ ∫ ω, (family p a).localDist η ω ∂S.v :=
    integral_nonneg (fun ω => (family p a).localDist_nonneg η ω)
  apply (ENNReal.ofReal_le_ofReal_iff hn).mp
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun ω => (family p a).localDist_nonneg η ω)]
  exact family_lintegral_localDist_ge_of_pure p a η hη

theorem family_localDist_latticeGaugeFamily_prime (p : Nat.Primes) (a : ℤ) :
    (family p a).localDist ((family p a).latticeGaugeFamily (family_isUltrametric p a))
      (primePoint p) = Real.log (p.val : ℝ) / 2 := by
  rw [← NormFamily.finiteImpurityProfile_eq_localDist_latticeGaugeFamily,
    finiteImpurityProfile, if_pos (primePoint_mem_fin p), family_completedUnitBallImpurity_prime]

theorem family_lintegral_localDist_latticeGaugeFamily (p : Nat.Primes) (a : ℤ) :
    (∫⁻ ω, ENNReal.ofReal ((family p a).localDist
      ((family p a).latticeGaugeFamily (family_isUltrametric p a)) ω) ∂S.v) =
        ENNReal.ofReal (Real.log (p.val : ℝ) / 2) := by
  rw [← NormFamily.globalImpurity_eq_lintegral_localDist_latticeGaugeFamily, family_globalImpurity]

theorem family_integral_localDist_latticeGaugeFamily (p : Nat.Primes) (a : ℤ) :
    (∫ ω, (family p a).localDist
      ((family p a).latticeGaugeFamily (family_isUltrametric p a)) ω ∂S.v) =
        Real.log (p.val : ℝ) / 2 := by
  have hI := ((family p a).globalImpurity_ne_top_iff_integrable_localDist_latticeGaugeFamily
    (family_isUltrametric p a)).mp (by rw [family_globalImpurity]; exact ENNReal.ofReal_ne_top)
  have hn := fun ω => (family p a).localDist_nonneg
    ((family p a).latticeGaugeFamily (family_isUltrametric p a)) ω
  have he := ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hn)
  rw [family_lintegral_localDist_latticeGaugeFamily] at he
  have h := congrArg ENNReal.toReal he
  have hhalf : 0 ≤ Real.log (p.val : ℝ) / 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast p.property.one_le)) (by norm_num)
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hn),
    ENNReal.toReal_ofReal hhalf] using h

end ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction

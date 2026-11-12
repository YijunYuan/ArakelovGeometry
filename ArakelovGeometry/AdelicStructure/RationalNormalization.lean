/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Examples.RationalFunction.Construction
public import Mathlib.Analysis.Normed.Field.Instances

import ArakelovGeometry.Analysis.AbsoluteValue.NormalizedCompletion
import ArakelovGeometry.MeasureTheory.Integral.FiniteSupport

/-!
# The standard normalized rational adelic structure

The source rational curve has one place for every rational prime, each of
mass one with `|p| = p⁻¹`, and one real place of mass one. It reuses the
actual rational absolute values already constructed in the rational-function
example. The general number-field model is not changed.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.AdelicStructure

noncomputable section

open AdelicCurve.RationalFunction

/-- The source's rational prime component, with counting measure. -/
abbrev rationalPrimeAdelicStructure : AdelicStructure ℚ where
  Ω := Nat.Primes
  A := primeMeasurableSpace
  v := Measure.count
  ϕ := rationalPadicAbv
  measurable_log _ _ := measurable_from_top
  integrable_log q hq := by
    apply integrable_of_support_subset_finset
      (s := (finite_rationalPadicAbv_ne_one hq).toFinset)
    · intro p hp
      apply (finite_rationalPadicAbv_ne_one hq).mem_toFinset.mpr
      intro h
      exact hp (by simp only [h, Real.log_one])
    · intro p _
      simp

/-- The actual source rational curve: all rational primes and one real place. -/
abbrev rationalAdelicStructure : AdelicStructure ℚ where
  Ω := Nat.Primes ⊕ Unit
  A := Sum.instMeasurableSpace
  v := (Measure.count : Measure Nat.Primes).map (@Sum.inl Nat.Primes Unit) +
    (Measure.dirac ()).map (@Sum.inr Nat.Primes Unit)
  ϕ := Sum.elim rationalPadicAbv (fun _ ↦ Rat.AbsoluteValue.real)
  measurable_log q hq :=
    measurable_fun_sum (rationalPrimeAdelicStructure.measurable_log q hq)
      (rationalInfiniteAdelicStructure.measurable_log q hq)
  integrable_log q hq :=
    (rationalPrimeAdelicStructure.amalgamation rationalInfiniteAdelicStructure).integrable_log
      q hq

@[simp]
theorem rationalAdelicStructure_phi_prime (p : Nat.Primes) :
    rationalAdelicStructure.ϕ (Sum.inl p) = rationalPadicAbv p := rfl

@[simp]
theorem rationalAdelicStructure_phi_infinite :
    rationalAdelicStructure.ϕ (Sum.inr ()) = Rat.AbsoluteValue.real := rfl

/-- The finite normalization is the source value `|p| = 1/p`. -/
theorem rationalAdelicStructure_prime_apply_prime (p : Nat.Primes) :
    rationalAdelicStructure.ϕ (Sum.inl p) (p.val : ℚ) = (p.val : ℝ)⁻¹ := by
  let : Fact p.val.Prime := ⟨p.property⟩
  change (padicNorm p.val (p.val : ℚ) : ℝ) = _
  rw [padicNorm.padicNorm_p_of_prime]
  simp only [Rat.cast_inv, Rat.cast_natCast]

@[simp]
theorem rationalAdelicStructure_prime_mem_fin (p : Nat.Primes) :
    Sum.inl p ∈ rationalAdelicStructure.Ωfin :=
  isNonarchimedean_rationalPadicAbv p

@[simp]
theorem rationalAdelicStructure_infinite_mem_inf :
    Sum.inr () ∈ rationalAdelicStructure.Ωinf := by
  intro h
  have hh := h (1 : ℚ) 1
  change Rat.AbsoluteValue.real (1 + 1) ≤
    max (Rat.AbsoluteValue.real 1) (Rat.AbsoluteValue.real 1) at hh
  norm_num [Rat.AbsoluteValue.real_eq_abs] at hh

/-- There is precisely one actual infinite place. -/
theorem rationalAdelicStructure_Ωinf :
    rationalAdelicStructure.Ωinf = {Sum.inr ()} := by
  change {ω : Nat.Primes ⊕ Unit | ¬IsNonarchimedean
    ((Sum.elim rationalPadicAbv (fun _ ↦ Rat.AbsoluteValue.real) ω :
      AbsoluteValue ℚ ℝ) : ℚ → ℝ)} = {Sum.inr ()}
  ext ω
  cases ω with
  | inl p =>
      simp only [Set.mem_singleton_iff, Sum.inl_ne_inr, iff_false]
      exact fun h ↦ h (isNonarchimedean_rationalPadicAbv p)
  | inr u =>
      cases u
      simp only [Set.mem_singleton_iff, iff_true]
      exact rationalAdelicStructure_infinite_mem_inf

/-- The rational curve uses a discrete measurable space, exactly as the source. -/
instance rationalAdelicStructure_discrete :
    DiscreteMeasurableSpace rationalAdelicStructure.Ω := by
  change DiscreteMeasurableSpace (Nat.Primes ⊕ Unit)
  constructor
  intro s
  exact measurableSet_sum_iff.mpr ⟨by trivial,
    DiscreteMeasurableSpace.forall_measurableSet _⟩

instance rationalAdelicStructure_measurableSingleton :
    MeasurableSingletonClass rationalAdelicStructure.Ω where
  measurableSet_singleton _ := rationalAdelicStructure_discrete.forall_measurableSet _

/-- The original rational measure has mass one at infinity. -/
theorem rationalAdelicStructure_v_Ωinf :
    rationalAdelicStructure.v rationalAdelicStructure.Ωinf = 1 := by
  rw [rationalAdelicStructure_Ωinf]
  change (Measure.count.map (@Sum.inl Nat.Primes Unit) +
    (Measure.dirac ()).map (@Sum.inr Nat.Primes Unit)) {Sum.inr ()} = 1
  let : MeasurableSingletonClass (Nat.Primes ⊕ Unit) :=
    rationalAdelicStructure_measurableSingleton
  rw [Measure.add_apply, Measure.map_dirac,
    Measure.map_apply measurable_inl (measurableSet_singleton _)]
  have he : (Sum.inl : Nat.Primes → Nat.Primes ⊕ Unit) ⁻¹' {Sum.inr ()} = ∅ := by
    ext p
    simp
  rw [he]
  simp

/-- The existing completed norm is normalized, without changing any field instance. -/
theorem rationalAdelicStructure_isRCLike (ω : rationalAdelicStructure.Ω)
    (hω : ω ∈ rationalAdelicStructure.Ωinf) :
    IsRCLikeNormedField (rationalAdelicStructure.ϕ ω).Completion := by
  have he : ω = (Sum.inr () : rationalAdelicStructure.Ω) :=
    Set.mem_singleton_iff.mp (rationalAdelicStructure_Ωinf ▸ hω)
  clear hω
  subst ω
  apply isRCLikeNormedField_of_norm_two
  have hn : ‖algebraMap ℚ (rationalAdelicStructure.ϕ (Sum.inr ())).Completion (2 : ℚ)‖ =
      rationalAdelicStructure.ϕ (Sum.inr ()) (2 : ℚ) := by
    change ‖(WithAbs.toAbs (rationalAdelicStructure.ϕ (Sum.inr ())) (2 : ℚ) :
      (rationalAdelicStructure.ϕ (Sum.inr ())).Completion)‖ = _
    rw [UniformSpace.Completion.norm_coe]
    rfl
  have hv : rationalAdelicStructure.ϕ (Sum.inr ()) (2 : ℚ) = 2 := by
    change Rat.AbsoluteValue.real (2 : ℚ) = 2
    norm_num [Rat.AbsoluteValue.real_eq_abs]
  rw [hv] at hn
  simpa only [map_ofNat] using hn

/-- Every source rational prime has mass one in the actual measure. -/
theorem rationalAdelicStructure_v_prime (p : Nat.Primes) :
    rationalAdelicStructure.v {Sum.inl p} = 1 := by
  change (Measure.count.map (@Sum.inl Nat.Primes Unit) +
    (Measure.dirac ()).map (@Sum.inr Nat.Primes Unit)) {Sum.inl p} = 1
  let : MeasurableSingletonClass (Nat.Primes ⊕ Unit) :=
    rationalAdelicStructure_measurableSingleton
  let : MeasurableSingletonClass Nat.Primes := ⟨fun _ ↦ trivial⟩
  rw [Measure.add_apply, Measure.map_dirac,
    Measure.map_apply measurable_inl (measurableSet_singleton _)]
  have he : (Sum.inl : Nat.Primes → Nat.Primes ⊕ Unit) ⁻¹' {Sum.inl p} = {p} := by
    ext q
    simp
  rw [he]
  simp

private theorem rationalNormalizationMeasurableInl :
    MeasurableEmbedding (@Sum.inl Nat.Primes Unit) :=
  ⟨Sum.inl_injective, measurable_inl, fun _ hs ↦ hs.inl_image⟩

private theorem rationalNormalizationMeasurableInr :
    MeasurableEmbedding (@Sum.inr Nat.Primes Unit) :=
  ⟨Sum.inr_injective, measurable_inr, fun _ hs ↦ hs.inr_image⟩

/-- The actual integral splits into the prime sum and the real logarithm. -/
theorem rationalAdelicStructure_integral_log_split (q : ℚ) (hq : q ≠ 0) :
    (∫ ω, Real.log (rationalAdelicStructure.ϕ ω q) ∂rationalAdelicStructure.v) =
      (∫ p : Nat.Primes, Real.log (rationalPadicAbv p q) ∂Measure.count) +
        Real.log (Rat.AbsoluteValue.real q) := by
  have h := rationalAdelicStructure.integrable_log q hq
  change Integrable (fun ω : Nat.Primes ⊕ Unit ↦
    Real.log ((Sum.elim rationalPadicAbv (fun _ ↦ Rat.AbsoluteValue.real) ω :
      AbsoluteValue ℚ ℝ) q))
    ((Measure.count : Measure Nat.Primes).map (@Sum.inl Nat.Primes Unit) +
      (Measure.dirac ()).map (@Sum.inr Nat.Primes Unit)) at h
  change (∫ ω : Nat.Primes ⊕ Unit,
    Real.log ((Sum.elim rationalPadicAbv (fun _ ↦ Rat.AbsoluteValue.real) ω :
      AbsoluteValue ℚ ℝ) q)
    ∂((Measure.count : Measure Nat.Primes).map (@Sum.inl Nat.Primes Unit) +
      (Measure.dirac ()).map (@Sum.inr Nat.Primes Unit))) = _
  rw [integral_add_measure (integrable_add_measure.mp h).1 (integrable_add_measure.mp h).2,
    rationalNormalizationMeasurableInl.integral_map,
    rationalNormalizationMeasurableInr.integral_map]
  simp only [Sum.elim_inl, Sum.elim_inr, integral_dirac]

private theorem rationalNormalizationIntegralPrime (p : Nat.Primes) :
    (∫ q : Nat.Primes, Real.log (rationalPadicAbv q (p.val : ℚ)) ∂Measure.count) =
      -Real.log (p.val : ℝ) := by
  classical
  let : Fact p.val.Prime := ⟨p.property⟩
  let : MeasurableSingletonClass Nat.Primes := ⟨fun _ ↦ trivial⟩
  have he : (fun q : Nat.Primes ↦ Real.log (rationalPadicAbv q (p.val : ℚ))) =
      ({p} : Set Nat.Primes).indicator (fun _ ↦ -Real.log (p.val : ℝ)) := by
    funext q
    let : Fact q.val.Prime := ⟨q.property⟩
    by_cases hq : q = p
    · subst q
      rw [Set.indicator_of_mem (Set.mem_singleton _)]
      change Real.log (padicNorm p.val (p.val : ℚ) : ℝ) = _
      rw [padicNorm.padicNorm_p_of_prime]
      simp only [Rat.cast_inv, Rat.cast_natCast, Real.log_inv]
    · rw [Set.indicator_of_notMem (by simpa only [Set.mem_singleton_iff] using hq)]
      change Real.log (padicNorm q.val (p.val : ℚ) : ℝ) = 0
      have hv : q.val ≠ p.val := fun hv ↦ hq (Subtype.ext hv)
      rw [padicNorm.padicNorm_of_prime_of_ne hv]
      norm_num
  rw [he, integral_indicator_const _ (measurableSet_singleton _)]
  simp

private theorem rationalNormalizationIntegralMul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    (∫ ω, Real.log (rationalAdelicStructure.ϕ ω (q * r)) ∂rationalAdelicStructure.v) =
      (∫ ω, Real.log (rationalAdelicStructure.ϕ ω q) ∂rationalAdelicStructure.v) +
        (∫ ω, Real.log (rationalAdelicStructure.ϕ ω r) ∂rationalAdelicStructure.v) := by
  have he : (fun ω ↦ Real.log (rationalAdelicStructure.ϕ ω (q * r))) =
      (fun ω ↦ Real.log (rationalAdelicStructure.ϕ ω q) +
        Real.log (rationalAdelicStructure.ϕ ω r)) := by
    funext ω
    rw [map_mul, Real.log_mul (rationalAdelicStructure.ϕ ω |>.pos hq).ne'
      (rationalAdelicStructure.ϕ ω |>.pos hr).ne']
  rw [he, integral_add (rationalAdelicStructure.integrable_log q hq)
    (rationalAdelicStructure.integrable_log r hr)]

private theorem rationalNormalizationIntegralNat (n : ℕ) :
    (∫ ω, Real.log (rationalAdelicStructure.ϕ ω (n : ℚ)) ∂rationalAdelicStructure.v) = 0 := by
  refine Nat.recOnMul ?_ ?_ ?_ ?_ n
  · simp only [Nat.cast_zero, map_zero, Real.log_zero, integral_zero]
  · simp only [Nat.cast_one, map_one, Real.log_one, integral_zero]
  · intro p hp
    rw [rationalAdelicStructure_integral_log_split _ (Nat.cast_ne_zero.mpr hp.ne_zero),
      rationalNormalizationIntegralPrime (⟨p, hp⟩ : Nat.Primes)]
    have he : Rat.AbsoluteValue.real (p : ℚ) = (p : ℝ) := by
      simp [Rat.AbsoluteValue.real_eq_abs]
    rw [he]
    exact neg_add_cancel _
  · intro a b ha hb
    by_cases ha0 : a = 0
    · simp [ha0]
    by_cases hb0 : b = 0
    · simp [hb0]
    rw [Nat.cast_mul, rationalNormalizationIntegralMul
      (Nat.cast_ne_zero.mpr ha0) (Nat.cast_ne_zero.mpr hb0), ha, hb, add_zero]

private theorem rationalNormalizationIntegralInt (n : ℤ) :
    (∫ ω, Real.log (rationalAdelicStructure.ϕ ω (n : ℚ)) ∂rationalAdelicStructure.v) = 0 := by
  cases n with
  | ofNat n => exact rationalNormalizationIntegralNat n
  | negSucc n =>
      simpa only [Int.cast_negSucc, AbsoluteValue.map_neg] using
        rationalNormalizationIntegralNat (n + 1)

/-- The source-normalized rational curve is proper by prime factorization. -/
instance rationalAdelicStructure_isProper : rationalAdelicStructure.IsProper := by
  constructor
  intro q hq
  have hn : (q.num : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (Rat.num_ne_zero.mpr hq)
  have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have he : (fun ω ↦ Real.log (rationalAdelicStructure.ϕ ω q)) =
      (fun ω ↦ Real.log (rationalAdelicStructure.ϕ ω (q.num : ℚ)) -
        Real.log (rationalAdelicStructure.ϕ ω (q.den : ℚ))) := by
    funext ω
    conv_lhs => rw [← Rat.num_div_den q]
    rw [map_div₀, Real.log_div (rationalAdelicStructure.ϕ ω |>.pos hn).ne'
      (rationalAdelicStructure.ϕ ω |>.pos hd).ne']
  rw [he, integral_sub (rationalAdelicStructure.integrable_log _ hn)
    (rationalAdelicStructure.integrable_log _ hd), rationalNormalizationIntegralInt,
    rationalNormalizationIntegralNat, sub_self]

end

/-- The rational adelic curve uses the usual Archimedean norm. -/
instance rationalAdelicStructure_isArchimedeanNormalized :
    rationalAdelicStructure.IsArchimedeanNormalized :=
  ⟨rationalAdelicStructure_isRCLike⟩

end ArakelovGeometry.AdelicStructure

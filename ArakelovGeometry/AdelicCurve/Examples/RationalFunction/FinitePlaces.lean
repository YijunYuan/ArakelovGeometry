/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Defs
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
import ArakelovGeometry.AdelicCurve.Examples.FunctionFields
import ArakelovGeometry.MeasureTheory.Integral.FiniteSupport
import Mathlib.NumberTheory.MahlerMeasure

/-!
# Finite places of the rational-function adelic curve over the rationals

The horizontal places of Chen–Moriwaki §3.2.5 are the closed points of the
affine line over `ℚ`; their absolute values have base the Mahler measure of a
primitive integral defining polynomial. The vertical places are Gauss
extensions of the rational `p`-adic absolute values.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.AdelicCurve.RationalFunction

open MeasureTheory Polynomial IsDedekindDomain HeightOneSpectrum AdelicStructure
open scoped ENNReal NNReal

/-- The closed points of the affine line over `ℚ`. -/
abbrev HorizontalPlace := HeightOneSpectrum ℚ[X]

instance horizontalMeasurableSpace : MeasurableSpace HorizontalPlace := ⊤

/-- A primitive integral defining polynomial for a horizontal closed point. -/
def horizontalPolynomial (v : HorizontalPlace) : ℤ[X] :=
  (IsLocalization.integerNormalization (nonZeroDivisors ℤ)
    (Submodule.IsPrincipal.generator v.asIdeal)).primPart

theorem horizontalPolynomial_isPrimitive (v : HorizontalPlace) :
    (horizontalPolynomial v).IsPrimitive :=
  Polynomial.isPrimitive_primPart _

theorem horizontalPolynomial_ne_zero (v : HorizontalPlace) :
    horizontalPolynomial v ≠ 0 :=
  Polynomial.primPart_ne_zero _

/-- The chosen primitive polynomial cuts out the given closed point. -/
theorem horizontalPolynomial_span (v : HorizontalPlace) :
    Ideal.span {(horizontalPolynomial v).map (algebraMap ℤ ℚ)} = v.asIdeal := by
  let q := Submodule.IsPrincipal.generator v.asIdeal
  let P := IsLocalization.integerNormalization (nonZeroDivisors ℤ) q
  have hq : q ≠ 0 := by
    intro h
    apply v.ne_bot
    rw [← Ideal.span_singleton_generator v.asIdeal]
    change Ideal.span {q} = ⊥
    rw [h, Ideal.span_singleton_eq_bot]
  have hP : P ≠ 0 := fun h ↦ hq (IsFractionRing.integerNormalization_eq_zero_iff.mp h)
  have hcontent : IsUnit (Polynomial.C (algebraMap ℤ ℚ P.content)) := by
    apply Polynomial.isUnit_C.mpr
    apply isUnit_iff_ne_zero.mpr
    exact (map_ne_zero_iff _ (algebraMap ℤ ℚ).injective_int).mpr
      (Polynomial.content_eq_zero_iff.not.mpr hP)
  obtain ⟨b, hb, hmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q
  have hb' : IsUnit (Polynomial.C (algebraMap ℤ ℚ b)) := by
    apply Polynomial.isUnit_C.mpr
    apply isUnit_iff_ne_zero.mpr
    exact (map_ne_zero_iff _ (algebraMap ℤ ℚ).injective_int).mpr
      (nonZeroDivisors.ne_zero hb)
  calc
    _ = Ideal.span {P.map (algebraMap ℤ ℚ)} := by
      conv_rhs => rw [P.eq_C_content_mul_primPart, Polynomial.map_mul, Polynomial.map_C]
      exact (Ideal.span_singleton_mul_left_unit hcontent _).symm
    _ = Ideal.span {q} := by
      rw [hmap, ← IsScalarTower.algebraMap_smul ℚ b q, ← Polynomial.C_mul',
        Ideal.span_singleton_mul_left_unit hb']
    _ = v.asIdeal := Ideal.span_singleton_generator v.asIdeal

/-- The Mahler measure `H(x)` used as the base of the horizontal absolute value. -/
def horizontalHeight (v : HorizontalPlace) : ℝ≥0 :=
  Real.toNNReal ((horizontalPolynomial v).map (Int.castRingHom ℂ)).mahlerMeasure

theorem one_le_horizontalHeight (v : HorizontalPlace) : 1 ≤ horizontalHeight v := by
  simpa only [horizontalHeight, Real.toNNReal_one] using (Real.toNNReal_le_toNNReal
    (Polynomial.one_le_mahlerMeasure_of_ne_zero (horizontalPolynomial_ne_zero v)))

open Classical in
/-- The horizontal absolute value `H(x)^(-ord_x)`. At height one it is the
trivial absolute value, including the necessary value zero at zero. -/
def horizontalAbv (v : HorizontalPlace) : AbsoluteValue (RatFunc ℚ) ℝ :=
  if h : 1 < horizontalHeight v then v.adicAbv h else AbsoluteValue.trivial

/-- Away from zero the horizontal absolute value has the source valuation formula. -/
theorem horizontalAbv_apply (v : HorizontalPlace) {f : RatFunc ℚ} (hf : f ≠ 0) :
    horizontalAbv v f =
      (horizontalHeight v : ℝ) ^ WithZero.log (v.valuation (RatFunc ℚ) f) := by
  classical
  unfold horizontalAbv
  split_ifs with h
  · change (WithZeroMulInt.toNNReal (ne_zero_of_lt h)
      (v.valuation (RatFunc ℚ) f) : ℝ) = _
    rw [WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff _).mpr hf),
      NNReal.coe_zpow]
  · have hv : horizontalHeight v = 1 := le_antisymm (not_lt.mp h) (one_le_horizontalHeight v)
    simp [AbsoluteValue.trivial_apply hf, hv]

/-- Horizontal absolute values are trivial on the coefficient field. -/
theorem horizontalAbv_rat (v : HorizontalPlace) (q : ℚ) :
    horizontalAbv v (algebraMap ℚ (RatFunc ℚ) q) =
      (AbsoluteValue.trivial : AbsoluteValue ℚ ℝ) q := by
  classical
  by_cases hq : q = 0
  · simp [hq]
  rw [horizontalAbv_apply v ((_root_.map_ne_zero _).mpr hq), AbsoluteValue.trivial_apply hq]
  have hval : v.valuation (RatFunc ℚ) (algebraMap ℚ (RatFunc ℚ) q) = 1 := by
    have heq : algebraMap ℚ (RatFunc ℚ) =
        (algebraMap ℚ[X] (RatFunc ℚ)).comp Polynomial.C := Subsingleton.elim _ _
    rw [heq]
    exact valuation_algebraMap_C v hq
  rw [hval, WithZero.log_one, zpow_zero]

/-- For each nonzero rational function, only finitely many horizontal logarithms are nonzero. -/
theorem finite_support_log_horizontalAbv {f : RatFunc ℚ} (hf : f ≠ 0) :
    (Function.support fun v : HorizontalPlace ↦ Real.log (horizontalAbv v f)).Finite := by
  have h := (finite_support_log hf).preimage ((Option.some_injective _).injOn)
  apply h.subset
  intro v hv
  change Real.log (pointAbv ℚ (some v) f) ≠ 0
  rw [pointAbv_some, real_log_adicAbv v hf]
  intro hz
  have hz' : WithZero.log (v.valuation (RatFunc ℚ) f) = 0 := by exact_mod_cast hz
  exact hv (by simp [horizontalAbv_apply v hf, hz'])

/-- Horizontal logarithmic evaluations are integrable for counting measure. -/
theorem integrable_log_horizontalAbv {f : RatFunc ℚ} (hf : f ≠ 0) :
    Integrable (fun v : HorizontalPlace ↦ Real.log (horizontalAbv v f)) Measure.count := by
  apply integrable_of_support_subset_finset
    (s := (finite_support_log_horizontalAbv hf).toFinset)
  · exact (finite_support_log_horizontalAbv hf).coe_toFinset.symm.subset
  · intro v _
    simp

/-- The horizontal counting-measure component of the rational-function adelic structure. -/
def horizontalAdelicStructure : AdelicStructure (RatFunc ℚ) where
  Ω := HorizontalPlace
  A := horizontalMeasurableSpace
  v := Measure.count
  ϕ := horizontalAbv
  measurable_log _ _ := measurable_from_top
  integrable_log _ hf := integrable_log_horizontalAbv hf

/-- The standard absolute value on `ℚ` at the prime `p`. -/
def rationalPadicAbv (p : Nat.Primes) : AbsoluteValue ℚ ℝ :=
  letI : Fact p.val.Prime := ⟨p.property⟩
  Rat.AbsoluteValue.padic p.val

instance primeMeasurableSpace : MeasurableSpace Nat.Primes := ⊤

theorem isNonarchimedean_rationalPadicAbv (p : Nat.Primes) :
    IsNonarchimedean (rationalPadicAbv p) := by
  let : Fact p.val.Prime := ⟨p.property⟩
  intro a b
  change (padicNorm p.val (a + b) : ℝ) ≤ max (padicNorm p.val a : ℝ) (padicNorm p.val b : ℝ)
  exact_mod_cast (padicNorm.nonarchimedean (p := p.val) (q := a) (r := b))

/-- The polynomial Gauss valuation at a rational prime, with values in `ℝ≥0`. -/
def primePolynomialValuation (p : Nat.Primes) : Valuation ℚ[X] ℝ≥0 where
  toFun P := ⟨Polynomial.gaussNorm (rationalPadicAbv p) 1 P,
    Polynomial.gaussNorm_nonneg _ _ zero_le_one⟩
  map_zero' := by
    apply NNReal.eq
    exact Polynomial.gaussNorm_zero (rationalPadicAbv p) 1
  map_one' := by
    apply NNReal.eq
    change Polynomial.gaussNorm (rationalPadicAbv p) 1 1 = 1
    rw [← Polynomial.C_1, Polynomial.gaussNorm_C, map_one]
  map_mul' P Q := by
    ext
    exact Polynomial.gaussNorm_mul (isNonarchimedean_rationalPadicAbv p) zero_lt_one P Q
  map_add_le_max' P Q :=
    Polynomial.isNonarchimedean_gaussNorm (rationalPadicAbv p)
      (isNonarchimedean_rationalPadicAbv p) zero_le_one P Q

theorem primePolynomialValuation_ne_zero (p : Nat.Primes) {P : ℚ[X]} (hP : P ≠ 0) :
    primePolynomialValuation p P ≠ 0 := by
  intro h
  have h' := congrArg (fun a : ℝ≥0 ↦ (a : ℝ)) h
  exact hP ((Polynomial.gaussNorm_eq_zero_iff (rationalPadicAbv p) P
    (fun _ h ↦ (rationalPadicAbv p).eq_zero.mp h) zero_lt_one).mp h')

/-- The Gauss valuation on the fraction field, obtained by localization. -/
def primeValuation (p : Nat.Primes) : Valuation (RatFunc ℚ) ℝ≥0 :=
  (primePolynomialValuation p).extendToLocalization
    (S := nonZeroDivisors ℚ[X])
    (fun _ h ↦ primePolynomialValuation_ne_zero p (nonZeroDivisors.ne_zero h))
    (RatFunc ℚ)

/-- The prime absolute value of §3.2.5 on `ℚ(T)`. -/
def primeAbv (p : Nat.Primes) : AbsoluteValue (RatFunc ℚ) ℝ where
  toFun f := primeValuation p f
  map_mul' f g := by simp
  nonneg' _ := NNReal.zero_le_coe
  eq_zero' f := by simp
  add_le' f g := le_trans ((primeValuation p).map_add f g)
    (max_le_add_of_nonneg NNReal.zero_le_coe NNReal.zero_le_coe)

/-- On a polynomial the prime absolute value is the maximum of the coefficient absolute values. -/
theorem primeAbv_polynomial (p : Nat.Primes) (P : ℚ[X]) :
    primeAbv p (algebraMap ℚ[X] (RatFunc ℚ) P) =
      Polynomial.gaussNorm (rationalPadicAbv p) 1 P := by
  change ((primeValuation p (algebraMap ℚ[X] (RatFunc ℚ) P) : ℝ≥0) : ℝ) = _
  exact congrArg (fun a : ℝ≥0 ↦ (a : ℝ))
    (Valuation.extendToLocalization_apply_map_apply (primePolynomialValuation p) _ (RatFunc ℚ) P)

/-- The prime absolute value is nonarchimedean. -/
theorem isNonarchimedean_primeAbv (p : Nat.Primes) :
    IsNonarchimedean (primeAbv p) := by
  intro f g
  exact_mod_cast (primeValuation p).map_add f g

/-- On rational functions the prime absolute value is the quotient of the two Gauss norms. -/
theorem primeAbv_num_div_denom (p : Nat.Primes) (f : RatFunc ℚ) :
    primeAbv p f = Polynomial.gaussNorm (rationalPadicAbv p) 1 f.num /
      Polynomial.gaussNorm (rationalPadicAbv p) 1 f.denom := by
  conv_lhs => rw [← RatFunc.num_div_denom f]
  rw [map_div₀, primeAbv_polynomial, primeAbv_polynomial]

/-- The prime absolute value restricts to the standard `p`-adic absolute value on `ℚ`. -/
theorem primeAbv_rat (p : Nat.Primes) (q : ℚ) :
    primeAbv p (algebraMap ℚ (RatFunc ℚ) q) = rationalPadicAbv p q := by
  have heq : algebraMap ℚ (RatFunc ℚ) =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp Polynomial.C := Subsingleton.elim _ _
  rw [heq, RingHom.comp_apply, primeAbv_polynomial, Polynomial.gaussNorm_C]

/-- Outside the prime divisors of a numerator and denominator, a rational has norm one. -/
theorem rationalPadicAbv_eq_one_of_large {q : ℚ} (hq : q ≠ 0) (p : Nat.Primes)
    (hp : max q.num.natAbs q.den < p.val) : rationalPadicAbv p q = 1 := by
  let : Fact p.val.Prime := ⟨p.property⟩
  have hnum : ¬(p.val : ℤ) ∣ q.num := by
    rw [Int.natCast_dvd]
    exact Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hq))
      (lt_of_le_of_lt (le_max_left _ _) hp)
  have hden : ¬p.val ∣ q.den :=
    Nat.not_dvd_of_pos_of_lt q.pos (lt_of_le_of_lt (le_max_right _ _) hp)
  change (padicNorm p.val q : ℝ) = 1
  have hn := (padicNorm.int_eq_one_iff (p := p.val) q.num).mpr hnum
  have hd := (padicNorm.nat_eq_one_iff (p := p.val) q.den).mpr hden
  rw [← Rat.num_div_den q, padicNorm.div, hn, hd]
  norm_num

/-- A nonzero rational has absolute value one at all but finitely many rational primes. -/
theorem finite_rationalPadicAbv_ne_one {q : ℚ} (hq : q ≠ 0) :
    {p : Nat.Primes | rationalPadicAbv p q ≠ 1}.Finite := by
  apply ((Set.finite_le_nat (max q.num.natAbs q.den)).preimage
    Subtype.val_injective.injOn).subset
  intro p hp
  exact le_of_not_gt fun h ↦ hp (rationalPadicAbv_eq_one_of_large hq p h)

/-- A nonzero polynomial has Gauss norm one at all but finitely many primes. -/
theorem finite_primeAbv_polynomial_ne_one {P : ℚ[X]} (hP : P ≠ 0) :
    {p : Nat.Primes | primeAbv p (algebraMap ℚ[X] (RatFunc ℚ) P) ≠ 1}.Finite := by
  classical
  have hbad : (⋃ i : P.support, {p : Nat.Primes |
      rationalPadicAbv p (P.coeff i) ≠ 1}).Finite :=
    Set.finite_iUnion fun i ↦
      finite_rationalPadicAbv_ne_one (Polynomial.mem_support_iff.mp i.property)
  apply hbad.subset
  intro p hp
  by_contra h
  have hall : ∀ i ∈ P.support, rationalPadicAbv p (P.coeff i) = 1 := by
    intro i hi
    exact not_ne_iff.mp fun hne ↦ h (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hne⟩)
  apply hp
  rw [primeAbv_polynomial, Polynomial.gaussNorm,
    dite_eq_left (Polynomial.support_nonempty.mpr hP)]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    simp [hall i hi]
  · obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hP
    simpa [hall i hi] using
      (Finset.le_sup' (fun i ↦ rationalPadicAbv p (P.coeff i) * (1 : ℝ) ^ i) hi)

/-- For a nonzero rational function, the logarithmic prime evaluations have finite support. -/
theorem finite_support_log_primeAbv {f : RatFunc ℚ} (hf : f ≠ 0) :
    (Function.support fun p : Nat.Primes ↦ Real.log (primeAbv p f)).Finite := by
  apply ((finite_primeAbv_polynomial_ne_one (RatFunc.num_ne_zero hf)).union
    (finite_primeAbv_polynomial_ne_one f.denom_ne_zero)).subset
  intro p hp
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  apply hp
  change Real.log (primeAbv p f) = 0
  rw [← RatFunc.num_div_denom f, map_div₀, h.1, h.2, div_self one_ne_zero, Real.log_one]

/-- Prime logarithmic evaluations are integrable for counting measure. -/
theorem integrable_log_primeAbv {f : RatFunc ℚ} (hf : f ≠ 0) :
    Integrable (fun p : Nat.Primes ↦ Real.log (primeAbv p f)) Measure.count := by
  apply integrable_of_support_subset_finset
    (s := (finite_support_log_primeAbv hf).toFinset)
  · exact (finite_support_log_primeAbv hf).coe_toFinset.symm.subset
  · intro p _
    simp

/-- The prime counting-measure component of the rational-function adelic structure. -/
def primeAdelicStructure : AdelicStructure (RatFunc ℚ) where
  Ω := Nat.Primes
  v := Measure.count
  ϕ := primeAbv
  measurable_log _ _ := measurable_of_countable _
  integrable_log _ hf := integrable_log_primeAbv hf

end ArakelovGeometry.AdelicCurve.RationalFunction

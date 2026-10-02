/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Examples.FunctionFields
import Mathlib.NumberTheory.MahlerMeasure
import Mathlib.NumberTheory.Ostrowski
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.RingTheory.Valuation.ExtendToLocalization

/-!
# Finite places of the rational-function adelic curve over the rationals

The horizontal places of Chen–Moriwaki §3.2.5 are the closed points of the
affine line over `ℚ`; their absolute values have base the Mahler measure of a
primitive integral defining polynomial. The vertical places are Gauss
extensions of the rational `p`-adic absolute values.
-/

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
      NNReal.coe_zpow, WithZero.toAdd_unzero_eq_log]
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

end ArakelovGeometry.AdelicCurve.RationalFunction

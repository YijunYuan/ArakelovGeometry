/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldLocalDeterminantIndex
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldLineIndex

/-!
# Actual prime orders and normalized determinant logarithms
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField WithZero

namespace ArakelovGeometry.NumberFieldFullLattice

open AdelicStructure ActualPrimeIndexing IsDiscreteValuationRing

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K : Type*} [Field K] [NumberField K]

private abbrev valuationCoefficientRing (p : HeightOneSpectrum (𝓞 K)) :=
  (normalizedNumberFieldAdelicStructure K).rationalLocalRing
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)

/-- The actual prime valuation has precisely the literal local coefficient ring as integers. -/
theorem rationalLocalRing_primeIntegers (p : HeightOneSpectrum (𝓞 K)) :
    (p.valuation K).Integers (valuationCoefficientRing p) := by
  change (p.valuation K).Integers
    ((normalizedNumberFieldAdelicStructure K).rationalLocalRing
      (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p))
  have heq := (normalizedNumberFieldAdelicStructure K).rationalLocalRing_eq_finitePlaceInteger
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)
    (FinitePlace.mk p) (NormFamily.normalizedPrimeValue_isEquiv p)
  simp only [FinitePlace.maximalIdeal_mk] at heq
  rw [heq]
  exact Valuation.integer.integers _

/-- Intrinsic local irreducibles have order one for the actual integer-valued prime valuation. -/
theorem rationalLocal_irreducible_valuation (p : HeightOneSpectrum (𝓞 K))
    {π : valuationCoefficientRing p} (hπ : Irreducible π) :
    p.valuation K (π : K) = WithZero.exp (-1 : ℤ) := by
  let hv := rationalLocalRing_primeIntegers p
  have hpos := hv.valuation_irreducible_pos hπ
  have hlt := hv.valuation_irreducible_lt_one hπ
  obtain ⟨t, ht⟩ := p.valuation_exists_uniformizer K
  have htlt : p.valuation K t < 1 := by
    rw [ht, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨s, hs⟩ := hv.exists_of_le_one htlt.le
  have hsnu : ¬ IsUnit s := by
    intro hu
    have hsu := hv.one_of_isUnit hu
    rw [hs] at hsu
    exact (ne_of_lt htlt) hsu
  have hsm : s ∈ IsLocalRing.maximalIdeal (valuationCoefficientRing p) :=
    by simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hsnu
  rw [hπ.maximalIdeal_eq] at hsm
  have hdvd : π ∣ s := Ideal.mem_span_singleton.mp hsm
  have hle := hv.le_of_dvd hdvd
  rw [hs, ht] at hle
  change p.valuation K (π : K) < 1 at hlt
  change WithZero.exp (-1 : ℤ) ≤ p.valuation K (π : K) at hle
  have hne : p.valuation K (π : K) ≠ 0 := ne_of_gt hpos
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at hle
  have hlog : (p.valuation K (π : K)).log = -1 := by omega
  rw [← WithZero.exp_log hne, hlog]

/-- The signed actual prime logarithm is minus the finite intrinsic local order. -/
theorem rationalLocal_primeLog_eq_neg_addVal (p : HeightOneSpectrum (𝓞 K))
    (a : valuationCoefficientRing p) (ha : a ≠ 0) :
    (p.valuation K (a : K)).log = -((addVal (valuationCoefficientRing p) a).toNat : ℤ) := by
  obtain ⟨π, hπ⟩ := exists_irreducible (valuationCoefficientRing p)
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
  rw [addVal_def' u hπ, ENat.toNat_natCast]
  have hu : p.valuation K ((u : valuationCoefficientRing p) : K) = 1 :=
    (rationalLocalRing_primeIntegers p).valuation_unit u
  change (p.valuation K (((u : valuationCoefficientRing p) : K) * (π : K) ^ n)).log = -(n : ℤ)
  rw [map_mul, map_pow, hu, rationalLocal_irreducible_valuation p hπ, one_mul,
    WithZero.log_pow, WithZero.log_exp]
  simp

/-- The intrinsic DVR order is precisely the nonnegative actual prime order. -/
theorem rationalLocal_addVal_eq_primeOrder (p : HeightOneSpectrum (𝓞 K))
    (a : valuationCoefficientRing p) (ha : a ≠ 0) :
    addVal (valuationCoefficientRing p) a = ((-(p.valuation K (a : K)).log).toNat : ℕ∞) := by
  rw [rationalLocal_primeLog_eq_neg_addVal p a ha, neg_neg, Int.toNat_natCast]
  exact (ENat.natCast_toNat (addVal_eq_top_iff.not.mpr ha)).symm

/-- The actual normalized prime logarithm is minus its produced scale times local order. -/
theorem rationalLocal_normalized_log (p : HeightOneSpectrum (𝓞 K))
    (a : valuationCoefficientRing p) (ha : a ≠ 0) :
    Real.log ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p) (a : K)) =
      -normalizedPrimeLogScale p * ((addVal (valuationCoefficientRing p) a).toNat : ℝ) := by
  have haK : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
  rw [normalizedPrime_log_value p haK, rationalLocal_primeLog_eq_neg_addVal p a ha]
  push_cast
  ring

/-- The corresponding actual normalized absolute value, with no normalization premise. -/
theorem rationalLocal_normalized_value (p : HeightOneSpectrum (𝓞 K))
    (a : valuationCoefficientRing p) (ha : a ≠ 0) :
    (normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p) (a : K) =
      Real.exp (-normalizedPrimeLogScale p *
        ((addVal (valuationCoefficientRing p) a).toNat : ℝ)) := by
  rw [← rationalLocal_normalized_log p a ha, Real.exp_log]
  exact AbsoluteValue.pos _ (fun h => ha (Subtype.ext h))

variable {E : Type*} [AddCommGroup E] [Module K E]

/-- The matrix of the actual full local inclusion has nonzero determinant. -/
theorem rationalLocalLattice_det_ne_zero
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    (LinearMap.toMatrix (rationalLocalBasisFinrank L₀ hfg₀ hspan₀ p)
      (rationalLocalBasisFinrank L hfg hspan p) (rationalLocalLatticeInclusion h p)).det ≠ 0 := by
  let b := rationalLocalBasisFinrank L hfg hspan p
  let c := rationalLocalBasisFinrank L₀ hfg₀ hspan₀ p
  let e := b.equiv c (Equiv.refl _)
  let f := (rationalLocalLatticeInclusion h p).comp e.toLinearMap
  let := finite_rationalLocalSpan L hfg p
  let := free_rationalLocalSpan L hfg p
  have hf : Function.Injective f := (rationalLocalLatticeInclusion_injective h p).comp e.injective
  have hmat : LinearMap.toMatrix c b (rationalLocalLatticeInclusion h p) =
      LinearMap.toMatrix b b f := by
    ext i j
    simp [LinearMap.toMatrix_apply, f, e]
  intro hdet
  have hz : LinearMap.det f = 0 := by
    rw [← LinearMap.det_toMatrix b f, ← hmat]
    exact hdet
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hf)

/-- The original localized quotient has finite module length. -/
theorem rationalLocalLattice_length_ne_top
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    Module.length (valuationCoefficientRing p)
      (rationalLocalSpan L p ⧸ rationalLocalLatticeImage h p) ≠ ⊤ := by
  rw [rationalLocalLattice_length_eq_addVal_det L₀ L h hfg₀ hfg hspan₀ hspan p]
  exact addVal_eq_top_iff.not.mpr (rationalLocalLattice_det_ne_zero L₀ L h hfg₀ hfg hspan₀ hspan p)

/-- The actual normalized finite-place determinant logarithm equals the actual quotient length
times the produced local scale. -/
theorem rationalLocalLattice_normalized_log_det
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    Real.log ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)
      ((LinearMap.toMatrix (rationalLocalBasisFinrank L₀ hfg₀ hspan₀ p)
        (rationalLocalBasisFinrank L hfg hspan p) (rationalLocalLatticeInclusion h p)).det : K)) =
      -normalizedPlaceLogScale (normalizedPrimeParameter p) *
        ((Module.length (valuationCoefficientRing p)
          (rationalLocalSpan L p ⧸ rationalLocalLatticeImage h p)).toNat : ℝ) := by
  rw [normalizedPlaceLogScale_prime,
    rationalLocalLattice_length_eq_addVal_det L₀ L h hfg₀ hfg hspan₀ hspan p]
  exact rationalLocal_normalized_log p _
    (rationalLocalLattice_det_ne_zero L₀ L h hfg₀ hfg hspan₀ hspan p)

end ArakelovGeometry.NumberFieldFullLattice

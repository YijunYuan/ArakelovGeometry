/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldFullLatticeGauge

/-!
# Literal global balls of arbitrary full number-field lattices

The actual completed/rational coefficient test and denominator-ideal argument
recover the originally prescribed lattice from every finite completed gauge.
The canonical integral action is used throughout. No regularity is required
of the prescribed infinite norms. Associated Spec sheaves are a separate cone.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct
noncomputable section

namespace ArakelovGeometry.NumberFieldFullLattice

open AdelicStructure ActualPrimeIndexing
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

local notation "N" => normalizedNumberFieldAdelicStructure K
local notation "R" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  AdelicStructure.rationalLocalRing (N) (normalizedPrimeParameter p)
    (normalizedPrimeParameter_mem_fin p)
local notation "F" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  AbsoluteValue.Completion (AdelicStructure.ϕ (N) (normalizedPrimeParameter p))
local notation "O" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  AdelicStructure.completedLocalRing (N) (normalizedPrimeParameter p)
    (normalizedPrimeParameter_mem_fin p)

/-- Actual rational coordinates of a vector in the produced local lattice. -/
theorem rationalLocalGenericBasis_repr_coe (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (y : rationalLocalSpan L p)
    (i : Fin (Module.finrank (R p) (rationalLocalSpan L p))) :
    (rationalLocalGenericBasis L hfg hspan p).repr (y : E) i =
      ((rationalLocalBasis L hfg p).repr y i : K) := by
  have hy : (y : E) = rationalLocalGenericEquiv L hspan p
      ((1 : K) ⊗ₜ[R p] y) := by
    rw [rationalLocalGenericEquiv_tmul, one_smul]
  rw [hy, rationalLocalGenericBasis, Module.Basis.map_repr]
  change ((rationalLocalBasis L hfg p).baseChange K).repr
    ((rationalLocalGenericEquiv L hspan p).symm
      (rationalLocalGenericEquiv L hspan p (1 ⊗ₜ[R p] y))) i = _
  rw [LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul]
  simp only [Algebra.smul_def, mul_one]
  rfl

/-- The literal rational localization is exactly the produced integral-coordinate condition. -/
theorem mem_rationalLocalSpan_iff_coefficients (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) (x : E) :
    x ∈ rationalLocalSpan L p ↔
      ∀ i, (rationalLocalGenericBasis L hfg hspan p).repr x i ∈ R p := by
  classical
  constructor
  · intro hx i
    rw [rationalLocalGenericBasis_repr_coe L hfg hspan p ⟨x, hx⟩ i]
    exact ((rationalLocalBasis L hfg p).repr ⟨x, hx⟩ i).property
  · intro hx
    rw [← (rationalLocalGenericBasis L hfg hspan p).sum_repr x]
    apply Submodule.sum_mem
    intro i _
    rw [rationalLocalGenericBasis_coe]
    exact (rationalLocalSpan L p).smul_mem
      ⟨(rationalLocalGenericBasis L hfg hspan p).repr x i, hx i⟩
      (rationalLocalBasis L hfg p i).property

/-- Completion preserves the literal rational local-lattice membership test. -/
theorem tmul_mem_completedLatticeSpan_iff (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) (x : E) :
    (1 : F p) ⊗ₜ[K] x ∈ NumberFieldModel.completedLatticeSpan L p ↔
      x ∈ rationalLocalSpan L p := by
  rw [completedLatticeSpan_eq_localBasis L hfg hspan p,
    mem_rationalLocalSpan_iff_coefficients L hfg hspan p]
  change (∀ i, ((rationalLocalGenericBasis L hfg hspan p).baseChange (F p)).repr
    ((1 : F p) ⊗ₜ[K] x) i ∈ O p) ↔ _
  simp only [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one,
    AdelicStructure.mem_completedLocalRing, AdelicStructure.norm_algebraMap_eq_absValue,
    AdelicStructure.mem_rationalLocalRing]

/-- Actual local membership supplies a genuine denominator outside the corresponding prime. -/
theorem exists_prime_complement_smul_mem (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) (x : E) (hx : x ∈ rationalLocalSpan L p) :
    ∃ a : 𝓞 K, a ∉ p.asIdeal ∧ algebraMap (𝓞 K) K a • x ∈ L := by
  let := rationalCoefficients_isLocalization p
  obtain ⟨a, ha⟩ := multiple_mem_span_of_mem_localization_span
    p.asIdeal.primeCompl (R p) (L : Set E) x hx
  refine ⟨a.val, a.property, ?_⟩
  simpa only [Submodule.span_eq, Submonoid.smul_def, integralVector_smul] using ha

private def denominatorIdeal (L : Submodule (𝓞 K) E) (x : E) : Ideal (𝓞 K) where
  carrier := {a | a • x ∈ L}
  zero_mem' := by simp only [Set.mem_ofPred_eq, zero_smul, L.zero_mem]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, add_smul]
    exact L.add_mem ha hb
  smul_mem' := by
    intro a b hb
    change (a * b) • x ∈ L
    rw [mul_smul]
    exact L.smul_mem a hb

/-- Full rational span gives the literal prime-local intersection equality, without FG. -/
theorem mem_iff_mem_all_rationalLocalSpans (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) (x : E) :
    x ∈ L ↔ ∀ p : HeightOneSpectrum (𝓞 K), x ∈ rationalLocalSpan L p := by
  constructor
  · intro hx p
    exact Submodule.subset_span hx
  · intro hx
    by_contra hnot
    let D := denominatorIdeal L x
    have hD : D ≠ ⊤ := by
      intro heq
      have h1 : (1 : 𝓞 K) ∈ D := heq.symm ▸ Submodule.mem_top
      change (1 : 𝓞 K) • x ∈ L at h1
      exact hnot (by simpa only [one_smul] using h1)
    obtain ⟨P, hP, hDP⟩ := Ideal.exists_le_maximal D hD
    have hPne : P ≠ ⊥ := by
      obtain ⟨a, ha, haL⟩ := exists_integral_smul_mem L hspan x
      have haD : a ∈ D := haL
      intro heq
      exact ha ((Submodule.mem_bot (𝓞 K)).mp (heq ▸ hDP haD))
    let p : HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, hPne⟩
    obtain ⟨a, haP, haL⟩ := exists_prime_complement_smul_mem L p x (hx p)
    exact haP (hDP haL)

/-- The constructed finite rational ball is the actual rational local lattice. -/
theorem fullLatticeGaugeFamily_mem_rationalUnitBall_prime
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (N) E)
    (p : HeightOneSpectrum (𝓞 K)) (x : E) :
    x ∈ (fullLatticeGaugeFamily L hfg hspan η).rationalUnitBall
      (normalizedPrimeParameter p) ↔ x ∈ rationalLocalSpan L p := by
  change (fullLatticeGaugeFamily L hfg hspan η).norm (normalizedPrimeParameter p)
    ((1 : F p) ⊗ₜ[K] x) ≤ 1 ↔ _
  rw [fullLatticeGaugeFamily_norm_prime,
    scalarLatticeGauge_le_one_iff_completedLatticeSpan L hfg hspan p]
  exact tmul_mem_completedLatticeSpan_iff L hfg hspan p x

/-- The literal global finite unit ball is exactly the originally prescribed lattice. -/
theorem fullLatticeGaugeFamily_globalUnitBall_eq (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (N) E) :
    (fullLatticeGaugeFamily L hfg hspan η).globalUnitBall = (L : Set E) := by
  ext x
  change x ∈ (fullLatticeGaugeFamily L hfg hspan η).globalUnitBall ↔ x ∈ L
  rw [NormFamily.mem_globalUnitBall, mem_iff_mem_all_rationalLocalSpans L hspan x]
  constructor
  · intro hx p
    exact (fullLatticeGaugeFamily_mem_rationalUnitBall_prime L hfg hspan η p x).mp
      (hx _ (normalizedPrimeParameter_mem_fin p))
  · intro hx ω hω
    obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
    exact (fullLatticeGaugeFamily_mem_rationalUnitBall_prime L hfg hspan η p x).mpr (hx p)

/-- The equality is literal also for the canonical integral submodule, with any ultra proof. -/
theorem fullLatticeGaugeFamily_globalUnitBallModule_eq
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (N) E)
    (hξ : (fullLatticeGaugeFamily L hfg hspan η).IsUltrametric) :
    (fullLatticeGaugeFamily L hfg hspan η).globalUnitBallModule hξ = L := by
  apply SetLike.coe_injective
  exact fullLatticeGaugeFamily_globalUnitBall_eq L hfg hspan η

/-- The actual constructed model simultaneously retains infinite norms and realizes the lattice. -/
theorem fullLatticeGaugeFamily_model [FiniteDimensional K E]
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (N) E) :
    (∀ ω, ω ∉ (N).Ωfin →
      (fullLatticeGaugeFamily L hfg hspan η).norm ω = η.norm ω) ∧
    (fullLatticeGaugeFamily L hfg hspan η).IsUltrametric ∧
    (fullLatticeGaugeFamily L hfg hspan η).HasFiniteNormExceptions ∧
    (fullLatticeGaugeFamily L hfg hspan η).IsDominated ∧
    (fullLatticeGaugeFamily L hfg hspan η).globalUnitBall = (L : Set E) := by
  obtain ⟨hc, hd⟩ := fullLatticeGaugeFamily_coherent_and_dominated L hfg hspan η
  exact ⟨fullLatticeGaugeFamily_norm_not_finite L hfg hspan η,
    fullLatticeGaugeFamily_isUltrametric L hfg hspan η, hc, hd,
    fullLatticeGaugeFamily_globalUnitBall_eq L hfg hspan η⟩

end ArakelovGeometry.NumberFieldFullLattice

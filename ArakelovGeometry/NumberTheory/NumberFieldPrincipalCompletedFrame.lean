/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormFamilyNormalizedCompletedCoherence
public import ArakelovGeometry.NumberTheory.NumberFieldModelIntegralFrame

/-!
# Actual completed frames outside principal prime divisors

Actual scalar-unit localization and canonical completed tensor maps carry a
produced principal integral frame to the actual completed coefficient ring.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldModel

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

local notation "S₀" => normalizedNumberFieldAdelicStructure K
local notation "ωₚ" => (fun p : HeightOneSpectrum (𝓞 K) ↦ normalizedPrimeParameter p)
local notation "𝓞ᵥ" => (fun p : HeightOneSpectrum (𝓞 K) ↦
  AdelicStructure.completedLocalRing (normalizedNumberFieldAdelicStructure K)
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p))
local notation "Kᵥ" => (fun p : HeightOneSpectrum (𝓞 K) ↦
  AbsoluteValue.Completion
    (AdelicStructure.ϕ (normalizedNumberFieldAdelicStructure K) (normalizedPrimeParameter p)))

/-- An actual integral denominator outside an actual prime becomes a unit in
the actual completed coefficient ring, using the produced prime localization. -/
theorem isUnit_completed_integral_of_not_mem (f : 𝓞 K)
    (p : HeightOneSpectrum (𝓞 K)) (hp : f ∉ p.asIdeal) :
    IsUnit ((S₀).integralCompletedLocalCoefficientMap (ωₚ p)
      (normalizedPrimeParameter_mem_fin p) f) := by
  let : IsLocalization p.asIdeal.primeCompl
      ((S₀).rationalLocalRing (ωₚ p) (normalizedPrimeParameter_mem_fin p)) := by
    simpa only [FinitePlace.maximalIdeal_mk] using
      (S₀).isLocalization_rationalLocalRing_of_finitePlace (ωₚ p)
        (normalizedPrimeParameter_mem_fin p) (FinitePlace.mk p)
        (NormFamily.normalizedPrimeValue_isEquiv p)
  have hu := IsLocalization.map_units
    ((S₀).rationalLocalRing (ωₚ p) (normalizedPrimeParameter_mem_fin p))
    (⟨f, hp⟩ : p.asIdeal.primeCompl)
  exact hu.map ((S₀).completedLocalCoefficientMap (ωₚ p)
    (normalizedPrimeParameter_mem_fin p))

/-- The actual principal-localization ring map to the actual completed valuation ring. -/
def principalToCompletedLocalRing (f : 𝓞 K) (p : HeightOneSpectrum (𝓞 K))
    (hp : f ∉ p.asIdeal) : Localization (Submonoid.powers f) →+* 𝓞ᵥ p :=
  IsLocalization.Away.lift f (isUnit_completed_integral_of_not_mem f p hp)

@[simp]
theorem principalToCompletedLocalRing_algebraMap (f : 𝓞 K)
    (p : HeightOneSpectrum (𝓞 K)) (hp : f ∉ p.asIdeal) (a : 𝓞 K) :
    principalToCompletedLocalRing f p hp (algebraMap (𝓞 K) (Localization (Submonoid.powers f)) a) =
      (S₀).integralCompletedLocalCoefficientMap (ωₚ p)
        (normalizedPrimeParameter_mem_fin p) a :=
  IsLocalization.Away.lift_eq f (isUnit_completed_integral_of_not_mem f p hp) a

/-- The original actual integral action agrees with its principal extension. -/
theorem principalCompletedScalarTower (f : 𝓞 K) (p : HeightOneSpectrum (𝓞 K))
    (hp : f ∉ p.asIdeal) :
    letI := (principalToCompletedLocalRing f p hp).toAlgebra
    IsScalarTower (𝓞 K) (Localization (Submonoid.powers f)) (𝓞ᵥ p) := by
  let := (principalToCompletedLocalRing f p hp).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a =>
    (principalToCompletedLocalRing_algebraMap f p hp a).symm

/-- The actual completed coefficient action agrees with original rational scalars. -/
theorem completedVector_integral_smul (p : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K)
    (x : Kᵥ p ⊗[K] E) :
    ((S₀).integralCompletedLocalCoefficientMap (ωₚ p)
      (normalizedPrimeParameter_mem_fin p) a) • x = (algebraMap (𝓞 K) K a) • x := by
  change (algebraMap K (Kᵥ p) (algebraMap (𝓞 K) K a)) • x = _
  exact IsScalarTower.algebraMap_smul (Kᵥ p) (algebraMap (𝓞 K) K a) x

/-- Actual integral and completed coefficient scalars agree on the original
completed tensor fibre with the canonical integral-vector module action. -/
theorem completedVector_integralScalarTower (p : HeightOneSpectrum (𝓞 K)) :
    @IsScalarTower (𝓞 K) (𝓞ᵥ p) (Kᵥ p ⊗[K] E)
      (inferInstance : Module (𝓞 K) (𝓞ᵥ p)).toSMul
      (inferInstance : Module (𝓞ᵥ p) (Kᵥ p ⊗[K] E)).toSMul
      (integralVectorModule (K := K) (E := Kᵥ p ⊗[K] E)).toSMul := by
  constructor
  intro a r x
  change (((S₀).integralCompletedLocalCoefficientMap (ωₚ p)
    (normalizedPrimeParameter_mem_fin p) a) * r) • x =
      (algebraMap (𝓞 K) K a) • (r • x)
  rw [mul_smul, completedVector_integral_smul]

/-- The actual original-vector inclusion into its actual completed tensor fibre. -/
def completedVectorMap (p : HeightOneSpectrum (𝓞 K)) : E →ₗ[𝓞 K] Kᵥ p ⊗[K] E :=
  ((TensorProduct.mk K (Kᵥ p) E) (1 : Kᵥ p)).restrictScalars (𝓞 K)

@[simp]
theorem completedVectorMap_apply (p : HeightOneSpectrum (𝓞 K)) (x : E) :
    completedVectorMap p x = (1 : Kᵥ p) ⊗ₜ[K] x := rfl

/-- The literal integral-lattice map into its actual completed tensor fibre. -/
def completedLatticeMap (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    L →ₗ[𝓞 K] Kᵥ p ⊗[K] E := (completedVectorMap p).comp L.subtype

/-- The canonical actual completed coefficient tensor map. -/
def completedLatticeTensorMap (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    𝓞ᵥ p ⊗[𝓞 K] L →ₗ[𝓞ᵥ p] Kᵥ p ⊗[K] E :=
  @LinearMap.liftBaseChange (𝓞 K) L (Kᵥ p ⊗[K] E) (𝓞ᵥ p) _ _ _ _ _ _
    (integralVectorModule (K := K)) _ (completedVector_integralScalarTower (E := E) p)
    (completedLatticeMap L p)

@[simp]
theorem completedLatticeTensorMap_tmul (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) (a : 𝓞ᵥ p) (x : L) :
    completedLatticeTensorMap L p (a ⊗ₜ[𝓞 K] x) = (a : Kᵥ p) ⊗ₜ[K] (x : E) := by
  change (a : Kᵥ p) • ((1 : Kᵥ p) ⊗ₜ[K] (x : E)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The actual completed lattice is the Oω-span of literal rational lattice images. -/
def completedLatticeSpan (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    Submodule (𝓞ᵥ p) (Kᵥ p ⊗[K] E) :=
  Submodule.span (𝓞ᵥ p) (Set.range fun x : L => (1 : Kᵥ p) ⊗ₜ[K] (x : E))

/-- The actual tensor image and literal completed span agree without a frame premise. -/
theorem range_completedLatticeTensorMap (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) :
    (completedLatticeTensorMap L p).range = completedLatticeSpan L p := by
  apply le_antisymm
  · rintro z ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      have hm := (completedLatticeSpan L p).smul_mem a
        (Submodule.subset_span (⟨x, rfl⟩ : _ ∈ Set.range _))
      rw [completedLatticeTensorMap_tmul]
      rw [TensorProduct.smul_tmul'] at hm
      change ((a : Kᵥ p) * 1) ⊗ₜ[K] (x : E) ∈ completedLatticeSpan L p at hm
      simpa only [mul_one] using hm
    | add x y hx hy =>
      simpa only [map_add] using (completedLatticeSpan L p).add_mem hx hy
  · apply Submodule.span_le.mpr
    rintro z ⟨x, rfl⟩
    refine ⟨1 ⊗ₜ[𝓞 K] x, ?_⟩
    rw [completedLatticeTensorMap_tmul]
    rfl

@[simp]
theorem principalGenericMap_mk (L : Submodule (𝓞 K) E) (f : 𝓞 K) (hf : f ≠ 0)
    (x : L) :
    principalGenericMap L f hf (LocalizedModule.mkLinearMap (Submonoid.powers f) L x) = x := by
  let : IsLocalizedModule (nonZeroDivisors (𝓞 K)) (LinearMap.id : E →ₗ[𝓞 K] E) :=
    isLocalizedModule_id (nonZeroDivisors (𝓞 K)) E K
  let hu := fun s : Submonoid.powers f =>
    IsLocalizedModule.map_units (LinearMap.id : E →ₗ[𝓞 K] E)
      ⟨s.1, (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hf)) s.2⟩
  exact LinearMap.congr_fun (LocalizedModule.lift_comp (Submonoid.powers f) L.subtype hu) x

/-- The actual principal-localized module maps to the original completed fibre. -/
def completedPrincipalMap (L : Submodule (𝓞 K) E) (f : 𝓞 K) (hf : f ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) :
    LocalizedModule.Away f L →ₗ[𝓞 K] Kᵥ p ⊗[K] E :=
  (completedVectorMap p).comp (principalGenericMap L f hf)

@[simp]
theorem completedPrincipalMap_mk (L : Submodule (𝓞 K) E) (f : 𝓞 K) (hf : f ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (x : L) :
    completedPrincipalMap L f hf p
      (LocalizedModule.mkLinearMap (Submonoid.powers f) L x) = (1 : Kᵥ p) ⊗ₜ[K] (x : E) := by
  change (1 : Kᵥ p) ⊗ₜ[K] principalGenericMap L f hf
    (LocalizedModule.mkLinearMap (Submonoid.powers f) L x) = _
  rw [principalGenericMap_mk]

/-- Actual localized denominators are units off their divisor, so their
module images stay in the literal completed lattice. -/
theorem completedPrincipalMap_mem_span (L : Submodule (𝓞 K) E)
    (f : 𝓞 K) (hf : f ≠ 0) (p : HeightOneSpectrum (𝓞 K)) (hp : f ∉ p.asIdeal)
    (x : LocalizedModule.Away f L) :
    completedPrincipalMap L f hf p x ∈ completedLatticeSpan L p := by
  obtain ⟨⟨l, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) L) x
  change (s : 𝓞 K) • x = LocalizedModule.mkLinearMap (Submonoid.powers f) L l at hs
  have hle : Submonoid.powers f ≤ p.asIdeal.primeCompl := Submonoid.powers_le.mpr hp
  have hsnot : (s : 𝓞 K) ∉ p.asIdeal := hle s.property
  obtain ⟨u, hu⟩ := isUnit_completed_integral_of_not_mem (s : 𝓞 K) p hsnot
  have hm : (u : 𝓞ᵥ p) • completedPrincipalMap L f hf p x ∈ completedLatticeSpan L p := by
    rw [hu]
    rw [completedVector_integral_smul]
    have he : completedPrincipalMap L f hf p ((s : 𝓞 K) • x) =
        (algebraMap (𝓞 K) K (s : 𝓞 K)) • completedPrincipalMap L f hf p x :=
      (completedPrincipalMap L f hf p).map_smul (s : 𝓞 K) x
    rw [← he]
    rw [hs, completedPrincipalMap_mk]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hh := (completedLatticeSpan L p).smul_mem (↑u⁻¹ : 𝓞ᵥ p) hm
  simpa only [← mul_smul, Units.inv_mul, one_smul] using hh

/-- A genuine principal integral basis produces the actual completed span
equality at every actual prime outside its denominator divisor. -/
theorem completedLatticeSpan_eq_basis_of_principal_frame (L : Submodule (𝓞 K) E)
    (f : 𝓞 K) (hf : f ≠ 0) {ι : Type*} [Finite ι] (b : Module.Basis ι K E)
    (bl : Module.Basis ι (Localization (Submonoid.powers f)) (LocalizedModule.Away f L))
    (hbl : ∀ i, principalGenericMap L f hf (bl i) = b i)
    (p : HeightOneSpectrum (𝓞 K)) (hp : f ∉ p.asIdeal) :
    completedLatticeSpan L p =
      Submodule.span (𝓞ᵥ p) (Set.range fun i => (1 : Kᵥ p) ⊗ₜ[K] b i) := by
  classical
  let := Fintype.ofFinite ι
  let A := Localization (Submonoid.powers f)
  let : Module A (Kᵥ p ⊗[K] E) :=
    Module.compHom (Kᵥ p ⊗[K] E) (principalToCompletedLocalRing f p hp)
  let : SMul (𝓞 K) (Kᵥ p ⊗[K] E) :=
    (integralVectorModule (K := K) (E := Kᵥ p ⊗[K] E)).toSMul
  let : IsScalarTower (𝓞 K) A (Kᵥ p ⊗[K] E) := by
    apply IsScalarTower.of_algebraMap_smul
    intro a z
    change principalToCompletedLocalRing f p hp (algebraMap (𝓞 K) A a) • z =
      (algebraMap (𝓞 K) K a) • z
    rw [principalToCompletedLocalRing_algebraMap]
    exact completedVector_integral_smul p a z
  let q := (completedPrincipalMap L f hf p).extendScalarsOfIsLocalization
    (Submonoid.powers f) A
  have hqi (i : ι) : q (bl i) = (1 : Kᵥ p) ⊗ₜ[K] b i := by
    change (1 : Kᵥ p) ⊗ₜ[K] principalGenericMap L f hf (bl i) = _
    rw [hbl]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, rfl⟩
    dsimp only
    let y := LocalizedModule.mkLinearMap (Submonoid.powers f) L x
    have hqy : q y = (1 : Kᵥ p) ⊗ₜ[K] (x : E) := completedPrincipalMap_mk L f hf p x
    rw [← hqy, ← bl.sum_repr y, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    change principalToCompletedLocalRing f p hp ((bl.repr y) i) • q (bl i) ∈ _
    rw [hqi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    dsimp only
    rw [← hqi i]
    exact completedPrincipalMap_mem_span L f hf p hp (bl i)

/-- Literal finite generation and full rational span produce a finite actual
prime-divisor exception set for any prescribed rational basis. -/
theorem exists_completed_integral_frame (L : Submodule (𝓞 K) E) (hFG : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K E) :
    ∃ f : 𝓞 K, f ≠ 0 ∧ {p : HeightOneSpectrum (𝓞 K) | f ∈ p.asIdeal}.Finite ∧
      ∀ p : HeightOneSpectrum (𝓞 K), f ∉ p.asIdeal →
        completedLatticeSpan L p =
          NormFamily.completedBasisLattice (S₀) b (ωₚ p)
            (normalizedPrimeParameter_mem_fin p) := by
  obtain ⟨f, hf, bl, hbl⟩ := exists_principal_integral_frame L hFG hspan b
  refine ⟨f, hf, finite_prime_divisors hf, ?_⟩
  intro p hp
  rw [NormFamily.completedBasisLattice_eq_span]
  exact completedLatticeSpan_eq_basis_of_principal_frame L f hf b bl hbl p hp

/-- The intrinsic completed scalar-infimum gauge is the genuine completed
basis norm outside the produced principal divisor. -/
theorem scalarLatticeGauge_completedLatticeSpan_of_principal_frame
    (L : Submodule (𝓞 K) E) (f : 𝓞 K) (hf : f ≠ 0) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K E)
    (bl : Module.Basis ι (Localization (Submonoid.powers f)) (LocalizedModule.Away f L))
    (hbl : ∀ i, principalGenericMap L f hf (bl i) = b i)
    (p : HeightOneSpectrum (𝓞 K)) (hp : f ∉ p.asIdeal) (z : Kᵥ p ⊗[K] E) :
    scalarLatticeGauge (F := Kᵥ p) (completedLatticeSpan L p : Set (Kᵥ p ⊗[K] E)) z =
      (NormFamily.ofBasis (S₀) E b).norm (ωₚ p) z := by
  rw [completedLatticeSpan_eq_basis_of_principal_frame L f hf b bl hbl p hp,
    ← NormFamily.completedBasisLattice_eq_span]
  exact NormFamily.scalarLatticeGauge_completedBasisLattice b (ωₚ p)
    (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm (ωₚ p))) z

/-- Literal finite generation and full span produce a common completed
frame for the actual intrinsic lattice gauge outside finite actual divisors. -/
theorem exists_completed_lattice_gauge_frame (L : Submodule (𝓞 K) E) (hFG : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K E) :
    ∃ f : 𝓞 K, f ≠ 0 ∧ {p : HeightOneSpectrum (𝓞 K) | f ∈ p.asIdeal}.Finite ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)), f ∉ p.asIdeal → ∀ z : Kᵥ p ⊗[K] E,
        scalarLatticeGauge (F := Kᵥ p) (completedLatticeSpan L p : Set (Kᵥ p ⊗[K] E)) z =
          (NormFamily.ofBasis (S₀) E b).norm (ωₚ p) z := by
  obtain ⟨f, hf, bl, hbl⟩ := exists_principal_integral_frame L hFG hspan b
  exact ⟨f, hf, finite_prime_divisors hf, fun p hp z =>
    scalarLatticeGauge_completedLatticeSpan_of_principal_frame L f hf b bl hbl p hp z⟩

end ArakelovGeometry.NumberFieldModel

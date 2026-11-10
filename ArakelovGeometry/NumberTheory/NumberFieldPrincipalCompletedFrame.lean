/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldModelIntegralFrame
import ArakelovGeometry.NumberTheory.NormFamilyNormalizedCompletedCoherence

/-!
# Actual completed frames outside principal prime divisors

Actual scalar-unit localization and canonical completed tensor maps carry a
produced principal integral frame to the actual completed coefficient ring.
-/

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldModel

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

private abbrev S := normalizedNumberFieldAdelicStructure K
private abbrev ω (p : HeightOneSpectrum (𝓞 K)) := normalizedPrimeParameter p
private abbrev O (p : HeightOneSpectrum (𝓞 K)) :=
  (S (K := K)).completedLocalRing (ω p) (normalizedPrimeParameter_mem_fin p)
private abbrev F (p : HeightOneSpectrum (𝓞 K)) := ((S (K := K)).ϕ (ω p)).Completion

/-- An actual integral denominator outside an actual prime becomes a unit in
the actual completed coefficient ring, using the produced prime localization. -/
theorem isUnit_completed_integral_of_not_mem (f : 𝓞 K)
    (p : HeightOneSpectrum (𝓞 K)) (hp : f ∉ p.asIdeal) :
    IsUnit ((S (K := K)).integralCompletedLocalCoefficientMap (ω p)
      (normalizedPrimeParameter_mem_fin p) f) := by
  let : IsLocalization p.asIdeal.primeCompl
      ((S (K := K)).rationalLocalRing (ω p) (normalizedPrimeParameter_mem_fin p)) := by
    simpa only [FinitePlace.maximalIdeal_mk] using
      (S (K := K)).isLocalization_rationalLocalRing_of_finitePlace (ω p)
        (normalizedPrimeParameter_mem_fin p) (FinitePlace.mk p)
        (NormFamily.normalizedPrimeValue_isEquiv p)
  have hu := IsLocalization.map_units
    ((S (K := K)).rationalLocalRing (ω p) (normalizedPrimeParameter_mem_fin p))
    (⟨f, hp⟩ : p.asIdeal.primeCompl)
  exact hu.map ((S (K := K)).completedLocalCoefficientMap (ω p)
    (normalizedPrimeParameter_mem_fin p))

/-- The actual principal-localization ring map to the actual completed valuation ring. -/
def principalToCompletedLocalRing (f : 𝓞 K) (p : HeightOneSpectrum (𝓞 K))
    (hp : f ∉ p.asIdeal) : Localization (Submonoid.powers f) →+* O p :=
  IsLocalization.Away.lift f (isUnit_completed_integral_of_not_mem f p hp)

@[simp]
theorem principalToCompletedLocalRing_algebraMap (f : 𝓞 K)
    (p : HeightOneSpectrum (𝓞 K)) (hp : f ∉ p.asIdeal) (a : 𝓞 K) :
    principalToCompletedLocalRing f p hp (algebraMap (𝓞 K) (Localization (Submonoid.powers f)) a) =
      (S (K := K)).integralCompletedLocalCoefficientMap (ω p)
        (normalizedPrimeParameter_mem_fin p) a :=
  IsLocalization.Away.lift_eq f (isUnit_completed_integral_of_not_mem f p hp) a

/-- The original actual integral action agrees with its principal extension. -/
theorem principalCompletedScalarTower (f : 𝓞 K) (p : HeightOneSpectrum (𝓞 K))
    (hp : f ∉ p.asIdeal) :
    letI := (principalToCompletedLocalRing f p hp).toAlgebra
    IsScalarTower (𝓞 K) (Localization (Submonoid.powers f)) (O p) := by
  let := (principalToCompletedLocalRing f p hp).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a =>
    (principalToCompletedLocalRing_algebraMap f p hp a).symm

/-- The actual completed coefficient action agrees with original rational scalars. -/
theorem completedVector_integral_smul (p : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K)
    (x : F p ⊗[K] E) :
    ((S (K := K)).integralCompletedLocalCoefficientMap (ω p)
      (normalizedPrimeParameter_mem_fin p) a) • x = (algebraMap (𝓞 K) K a) • x := by
  change (algebraMap K (F p) (algebraMap (𝓞 K) K a)) • x = _
  exact IsScalarTower.algebraMap_smul (F p) (algebraMap (𝓞 K) K a) x

/-- Actual integral and completed coefficient scalars agree on the original
completed tensor fibre with the canonical integral-vector module action. -/
theorem completedVector_integralScalarTower (p : HeightOneSpectrum (𝓞 K)) :
    @IsScalarTower (𝓞 K) (O p) (F p ⊗[K] E)
      (inferInstance : Module (𝓞 K) (O p)).toSMul
      (inferInstance : Module (O p) (F p ⊗[K] E)).toSMul
      (integralVectorModule (K := K) (E := F p ⊗[K] E)).toSMul := by
  constructor
  intro a r x
  change (((S (K := K)).integralCompletedLocalCoefficientMap (ω p)
    (normalizedPrimeParameter_mem_fin p) a) * r) • x =
      (algebraMap (𝓞 K) K a) • (r • x)
  rw [mul_smul, completedVector_integral_smul]

/-- The actual original-vector inclusion into its actual completed tensor fibre. -/
def completedVectorMap (p : HeightOneSpectrum (𝓞 K)) : E →ₗ[𝓞 K] F p ⊗[K] E :=
  ((TensorProduct.mk K (F p) E) (1 : F p)).restrictScalars (𝓞 K)

@[simp]
theorem completedVectorMap_apply (p : HeightOneSpectrum (𝓞 K)) (x : E) :
    completedVectorMap p x = (1 : F p) ⊗ₜ[K] x := rfl

/-- The literal integral-lattice map into its actual completed tensor fibre. -/
def completedLatticeMap (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    L →ₗ[𝓞 K] F p ⊗[K] E := (completedVectorMap p).comp L.subtype

/-- The canonical actual completed coefficient tensor map. -/
def completedLatticeTensorMap (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    O p ⊗[𝓞 K] L →ₗ[O p] F p ⊗[K] E :=
  @LinearMap.liftBaseChange (𝓞 K) L (F p ⊗[K] E) (O p) _ _ _ _ _ _
    (integralVectorModule (K := K)) _ (completedVector_integralScalarTower (E := E) p)
    (completedLatticeMap L p)

@[simp]
theorem completedLatticeTensorMap_tmul (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) (a : O p) (x : L) :
    completedLatticeTensorMap L p (a ⊗ₜ[𝓞 K] x) = (a : F p) ⊗ₜ[K] (x : E) := by
  change (a : F p) • ((1 : F p) ⊗ₜ[K] (x : E)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The actual completed lattice is the Oω-span of literal rational lattice images. -/
def completedLatticeSpan (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    Submodule (O p) (F p ⊗[K] E) :=
  Submodule.span (O p) (Set.range fun x : L => (1 : F p) ⊗ₜ[K] (x : E))

/-- The actual tensor image and literal completed span agree without a frame premise. -/
theorem range_completedLatticeTensorMap (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) :
    (completedLatticeTensorMap L p).range = completedLatticeSpan L p := by
  apply le_antisymm
  · rintro z ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have hm := (completedLatticeSpan L p).smul_mem a
        (Submodule.subset_span (⟨x, rfl⟩ : _ ∈ Set.range _))
      rw [completedLatticeTensorMap_tmul]
      rw [TensorProduct.smul_tmul'] at hm
      change ((a : F p) * 1) ⊗ₜ[K] (x : E) ∈ completedLatticeSpan L p at hm
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
    LocalizedModule.Away f L →ₗ[𝓞 K] F p ⊗[K] E :=
  (completedVectorMap p).comp (principalGenericMap L f hf)

@[simp]
theorem completedPrincipalMap_mk (L : Submodule (𝓞 K) E) (f : 𝓞 K) (hf : f ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (x : L) :
    completedPrincipalMap L f hf p
      (LocalizedModule.mkLinearMap (Submonoid.powers f) L x) = (1 : F p) ⊗ₜ[K] (x : E) := by
  change (1 : F p) ⊗ₜ[K] principalGenericMap L f hf
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
  have hm : (u : O p) • completedPrincipalMap L f hf p x ∈ completedLatticeSpan L p := by
    rw [hu]
    rw [completedVector_integral_smul]
    have he : completedPrincipalMap L f hf p ((s : 𝓞 K) • x) =
        (algebraMap (𝓞 K) K (s : 𝓞 K)) • completedPrincipalMap L f hf p x :=
      (completedPrincipalMap L f hf p).map_smul (s : 𝓞 K) x
    rw [← he]
    rw [hs, completedPrincipalMap_mk]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hh := (completedLatticeSpan L p).smul_mem (↑u⁻¹ : O p) hm
  simpa only [← mul_smul, Units.inv_mul, one_smul] using hh

/-- A genuine principal integral basis produces the actual completed span
equality at every actual prime outside its denominator divisor. -/
theorem completedLatticeSpan_eq_basis_of_principal_frame (L : Submodule (𝓞 K) E)
    (f : 𝓞 K) (hf : f ≠ 0) {ι : Type*} [Finite ι] (b : Module.Basis ι K E)
    (bl : Module.Basis ι (Localization (Submonoid.powers f)) (LocalizedModule.Away f L))
    (hbl : ∀ i, principalGenericMap L f hf (bl i) = b i)
    (p : HeightOneSpectrum (𝓞 K)) (hp : f ∉ p.asIdeal) :
    completedLatticeSpan L p =
      Submodule.span (O p) (Set.range fun i => (1 : F p) ⊗ₜ[K] b i) := by
  classical
  let := Fintype.ofFinite ι
  let A := Localization (Submonoid.powers f)
  let : Module A (F p ⊗[K] E) :=
    Module.compHom (F p ⊗[K] E) (principalToCompletedLocalRing f p hp)
  let : SMul (𝓞 K) (F p ⊗[K] E) :=
    (integralVectorModule (K := K) (E := F p ⊗[K] E)).toSMul
  let : IsScalarTower (𝓞 K) A (F p ⊗[K] E) := by
    apply IsScalarTower.of_algebraMap_smul
    intro a z
    change principalToCompletedLocalRing f p hp (algebraMap (𝓞 K) A a) • z =
      (algebraMap (𝓞 K) K a) • z
    rw [principalToCompletedLocalRing_algebraMap]
    exact completedVector_integral_smul p a z
  let q := (completedPrincipalMap L f hf p).extendScalarsOfIsLocalization
    (Submonoid.powers f) A
  have hqi (i : ι) : q (bl i) = (1 : F p) ⊗ₜ[K] b i := by
    change (1 : F p) ⊗ₜ[K] principalGenericMap L f hf (bl i) = _
    rw [hbl]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, rfl⟩
    dsimp only
    let y := LocalizedModule.mkLinearMap (Submonoid.powers f) L x
    have hqy : q y = (1 : F p) ⊗ₜ[K] (x : E) := completedPrincipalMap_mk L f hf p x
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
          NormFamily.completedBasisLattice (S (K := K)) b (ω p)
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
    (p : HeightOneSpectrum (𝓞 K)) (hp : f ∉ p.asIdeal) (z : F p ⊗[K] E) :
    scalarLatticeGauge (F := F p) (completedLatticeSpan L p : Set (F p ⊗[K] E)) z =
      (NormFamily.ofBasis (S (K := K)) E b).norm (ω p) z := by
  rw [completedLatticeSpan_eq_basis_of_principal_frame L f hf b bl hbl p hp,
    ← NormFamily.completedBasisLattice_eq_span]
  exact NormFamily.scalarLatticeGauge_completedBasisLattice b (ω p)
    (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm (ω p))) z

/-- Literal finite generation and full span produce a common completed
frame for the actual intrinsic lattice gauge outside finite actual divisors. -/
theorem exists_completed_lattice_gauge_frame (L : Submodule (𝓞 K) E) (hFG : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K E) :
    ∃ f : 𝓞 K, f ≠ 0 ∧ {p : HeightOneSpectrum (𝓞 K) | f ∈ p.asIdeal}.Finite ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)), f ∉ p.asIdeal → ∀ z : F p ⊗[K] E,
        scalarLatticeGauge (F := F p) (completedLatticeSpan L p : Set (F p ⊗[K] E)) z =
          (NormFamily.ofBasis (S (K := K)) E b).norm (ω p) z := by
  obtain ⟨f, hf, bl, hbl⟩ := exists_principal_integral_frame L hFG hspan b
  exact ⟨f, hf, finite_prime_divisors hf, fun p hp z =>
    scalarLatticeGauge_completedLatticeSpan_of_principal_frame L f hf b bl hbl p hp z⟩

end ArakelovGeometry.NumberFieldModel

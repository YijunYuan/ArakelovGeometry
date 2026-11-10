/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Completed
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.NumberTheory.NumberField.Model.Open.Lattice

/-!
# Actual arbitrary full integral lattices

The integral module is the literal submodule of the original rational space.
Its local bases and tensor identifications are produced from finite generation
and full rational span, independently of any norm-family certificate.
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

/-- The actual integral lattice is torsion-free under its canonical integral action. -/
theorem isTorsionFree (L : Submodule (𝓞 K) E) : Module.IsTorsionFree (𝓞 K) L := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a x h
  have hz : algebraMap (𝓞 K) K a • (x : E) = 0 := congrArg Subtype.val h
  rcases smul_eq_zero.mp hz with ha | hx
  · exact Or.inl ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mp ha)
  · exact Or.inr (Subtype.ext hx)

/-- Full rational span clears actual nonzero integral denominators in every vector. -/
theorem exists_integral_smul_mem (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) (x : E) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ algebraMap (𝓞 K) K a • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set E) := hspan.symm ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (𝓞 K)) K (L : Set E) x hx
  refine ⟨a.val, (mem_nonZeroDivisors_iff_ne_zero.mp a.property), ?_⟩
  simpa only [Submodule.span_eq, Submonoid.smul_def, integralVector_smul] using ha

/-- The literal inclusion realizes the rational space as localization of the full lattice. -/
theorem isLocalizedModule_generic (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) :
    IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by
  let : IsLocalizedModule (nonZeroDivisors (𝓞 K)) (LinearMap.id : E →ₗ[𝓞 K] E) :=
    isLocalizedModule_id (nonZeroDivisors (𝓞 K)) E K
  refine ⟨IsLocalizedModule.map_units (LinearMap.id : E →ₗ[𝓞 K] E), ?_, ?_⟩
  · intro x
    obtain ⟨a, ha, hax⟩ := exists_integral_smul_mem L hspan x
    exact ⟨(⟨algebraMap (𝓞 K) K a • x, hax⟩,
      ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩), rfl⟩
  · intro x y hxy
    exact ⟨1, by simpa using (Subtype.ext hxy : x = y)⟩

/-- The canonical generic tensor equivalence, with no projectivity or coherence premise. -/
def genericTensorEquiv (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) : K ⊗[𝓞 K] L ≃ₗ[K] E := by
  let := isLocalizedModule_generic L hspan
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K L.subtype).equiv

@[simp]
theorem genericTensorEquiv_tmul (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) (a : K) (x : L) :
    genericTensorEquiv L hspan (a ⊗ₜ[𝓞 K] x) = a • (x : E) := by
  let := isLocalizedModule_generic L hspan
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K L.subtype).equiv_tmul a x

/-- Every prime localization of the actual finite lattice is free, including the generic prime. -/
theorem free_prime_localization (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (P : Ideal (𝓞 K)) [P.IsPrime] :
    Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl L) := by
  let : Module.Finite (𝓞 K) L := Module.Finite.of_fg hfg
  let := isTorsionFree L
  infer_instance

/-- Projectivity of the actual lattice follows from produced prime-local freeness. -/
theorem projective (L : Submodule (𝓞 K) E) (hfg : L.FG) :
    Module.Projective (𝓞 K) L := by
  let : Module.Finite (𝓞 K) L := Module.Finite.of_fg hfg
  let := Module.finitePresentation_of_finite (𝓞 K) L
  apply NumberFieldOpenModel.projective_of_localizations_free
  intro P hP
  let := hP.isPrime
  exact free_prime_localization L hfg P

local notation "S₀" => normalizedNumberFieldAdelicStructure K
local notation "Rᵥ" => (fun p : HeightOneSpectrum (𝓞 K) ↦
  AdelicStructure.rationalLocalRing (normalizedNumberFieldAdelicStructure K)
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p))

local notation "Kᵥ" => (fun p : HeightOneSpectrum (𝓞 K) ↦
  AbsoluteValue.Completion
    (AdelicStructure.ϕ (normalizedNumberFieldAdelicStructure K) (normalizedPrimeParameter p)))
local notation "𝓞ᵥ" => (fun p : HeightOneSpectrum (𝓞 K) ↦
  AdelicStructure.completedLocalRing (normalizedNumberFieldAdelicStructure K)
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p))

/-- The original integral and rational-local scalar actions agree on E. -/
instance integralRationalLocalVectorScalarTower (p : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (Rᵥ p) E where
  smul_assoc a r x := by
    change (algebraMap (𝓞 K) K a * (r : K)) • x =
      algebraMap (𝓞 K) K a • ((r : K) • x)
    exact mul_smul _ _ _

/-- The literal scalar span of the full lattice in the actual rational valuation ring. -/
def rationalLocalSpan (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    Submodule (Rᵥ p) E := Submodule.span (Rᵥ p) (L : Set E)

/-- The original actual lattice includes in its literal rational local span. -/
def rationalLocalInclusion (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    L →ₗ[𝓞 K] rationalLocalSpan L p where
  toFun x := ⟨x.val, Submodule.subset_span x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual normalized rational coefficient ring is the actual prime localization. -/
theorem rationalCoefficients_isLocalization (p : HeightOneSpectrum (𝓞 K)) :
    IsLocalization p.asIdeal.primeCompl (Rᵥ p) := by
  have h := (S₀).isLocalization_rationalLocalRing_of_finitePlace
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)
    (FinitePlace.mk p) (NormFamily.normalizedPrimeValue_isEquiv p)
  simpa only [FinitePlace.maximalIdeal_mk] using h

/-- Prime-complement denominators realize the literal local span as the actual localization. -/
theorem isLocalizedModule_rationalLocalInclusion (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) :
    IsLocalizedModule p.asIdeal.primeCompl (rationalLocalInclusion L p) := by
  let := rationalCoefficients_isLocalization p
  let : IsLocalizedModule p.asIdeal.primeCompl
      (LinearMap.id : rationalLocalSpan L p →ₗ[𝓞 K] rationalLocalSpan L p) :=
    isLocalizedModule_id p.asIdeal.primeCompl (rationalLocalSpan L p) (Rᵥ p)
  refine ⟨IsLocalizedModule.map_units
    (LinearMap.id : rationalLocalSpan L p →ₗ[𝓞 K] rationalLocalSpan L p), ?_, ?_⟩
  · intro y
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span
      p.asIdeal.primeCompl (Rᵥ p) (L : Set E) (y : E) y.property
    have hdL : algebraMap (𝓞 K) K d • (y : E) ∈ L := by
      simpa only [Submodule.span_eq, Submonoid.smul_def, integralVector_smul] using hd
    exact ⟨(⟨algebraMap (𝓞 K) K d • (y : E), hdL⟩, d), rfl⟩
  · intro x y hxy
    have h : x = y := Subtype.ext (congrArg (fun z : rationalLocalSpan L p => (z : E)) hxy)
    exact ⟨1, by simpa using h⟩

/-- The literal local span is the image of the canonical actual local tensor inclusion. -/
def rationalLocalTensorEquiv (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) : (Rᵥ p) ⊗[𝓞 K] L ≃ₗ[Rᵥ p] rationalLocalSpan L p := by
  letI := rationalCoefficients_isLocalization p
  letI := isLocalizedModule_rationalLocalInclusion L p
  exact (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl
    (Rᵥ p) (rationalLocalInclusion L p)).equiv

@[simp]
theorem rationalLocalTensorEquiv_tmul (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) (a : Rᵥ p) (x : L) :
    (rationalLocalTensorEquiv L p (a ⊗ₜ[𝓞 K] x) : E) = (a : K) • (x : E) := by
  let := rationalCoefficients_isLocalization p
  let := isLocalizedModule_rationalLocalInclusion L p
  exact congrArg (fun z : rationalLocalSpan L p => (z : E))
    ((IsLocalizedModule.isBaseChange p.asIdeal.primeCompl
      (Rᵥ p) (rationalLocalInclusion L p)).equiv_tmul a x)

/-- The actual localized lattice is finite from its original finite generators. -/
theorem finite_rationalLocalSpan (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (p : HeightOneSpectrum (𝓞 K)) : Module.Finite (Rᵥ p) (rationalLocalSpan L p) := by
  let : Module.Finite (𝓞 K) L := Module.Finite.of_fg hfg
  exact Module.Finite.of_surjective (rationalLocalTensorEquiv L p).toLinearMap
    (rationalLocalTensorEquiv L p).surjective

/-- A produced free basis exists in every literal rational local span. -/
theorem free_rationalLocalSpan (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (p : HeightOneSpectrum (𝓞 K)) : Module.Free (Rᵥ p) (rationalLocalSpan L p) := by
  let := finite_rationalLocalSpan L hfg p
  let := (S₀).isPrincipalIdealRing_rationalLocalRing
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm
        (normalizedPrimeParameter p)))
  let : Module.IsTorsionFree (Rᵥ p) (rationalLocalSpan L p) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a x h
    have hz : (a : K) • (x : E) = 0 := congrArg Subtype.val h
    rcases smul_eq_zero.mp hz with ha | hx
    · exact Or.inl (Subtype.ext ha)
    · exact Or.inr (Subtype.ext hx)
  infer_instance

/-- The actual local span has the same original rational generic fibre. -/
theorem isLocalizedModule_rationalLocalGeneric (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    IsLocalizedModule (nonZeroDivisors (Rᵥ p)) (rationalLocalSpan L p).subtype := by
  let : IsLocalizedModule (nonZeroDivisors (Rᵥ p)) (LinearMap.id : E →ₗ[Rᵥ p] E) :=
    isLocalizedModule_id (nonZeroDivisors (Rᵥ p)) E K
  refine ⟨IsLocalizedModule.map_units (LinearMap.id : E →ₗ[Rᵥ p] E), ?_, ?_⟩
  · intro x
    obtain ⟨a, ha, hax⟩ := exists_integral_smul_mem L hspan x
    have haK : algebraMap (𝓞 K) K a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
    let d : Rᵥ p := ⟨algebraMap (𝓞 K) K a,
      ((S₀).mem_rationalLocalRing
        (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) _).mpr
        (NumberField.abs_le_one_of_isIntegral (normalizedPrimeParameter_mem_fin p)
          (NumberField.RingOfIntegers.isIntegral_coe a))⟩
    have hd : d ≠ 0 := fun h => haK (congrArg (fun r : Rᵥ p => (r : K)) h)
    exact ⟨(⟨algebraMap (𝓞 K) K a • x, Submodule.subset_span hax⟩,
      ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  · intro x y h
    exact ⟨1, by simpa using (Subtype.ext h : x = y)⟩

/-- The actual generic identification of the produced rational local module. -/
def rationalLocalGenericEquiv (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    K ⊗[Rᵥ p] rationalLocalSpan L p ≃ₗ[K] E := by
  letI := isLocalizedModule_rationalLocalGeneric L hspan p
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors (Rᵥ p))
    K (rationalLocalSpan L p).subtype).equiv

@[simp]
theorem rationalLocalGenericEquiv_tmul (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (a : K) (x : rationalLocalSpan L p) :
    rationalLocalGenericEquiv L hspan p (a ⊗ₜ[Rᵥ p] x) = a • (x : E) := by
  let := isLocalizedModule_rationalLocalGeneric L hspan p
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors (Rᵥ p))
    K (rationalLocalSpan L p).subtype).equiv_tmul a x

/-- A finite local basis is produced from actual finite generation and local freeness. -/
def rationalLocalBasis (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (p : HeightOneSpectrum (𝓞 K)) :
    Module.Basis (Fin (Module.finrank (Rᵥ p) (rationalLocalSpan L p)))
      (Rᵥ p) (rationalLocalSpan L p) := by
  letI := finite_rationalLocalSpan L hfg p
  letI := free_rationalLocalSpan L hfg p
  exact Module.finBasis _ _

/-- The produced actual local basis becomes a basis of the original rational vector space. -/
def rationalLocalGenericBasis (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    Module.Basis (Fin (Module.finrank (Rᵥ p) (rationalLocalSpan L p))) K E :=
  ((rationalLocalBasis L hfg p).baseChange K).map (rationalLocalGenericEquiv L hspan p)

@[simp]
theorem rationalLocalGenericBasis_coe (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (i : Fin (Module.finrank (Rᵥ p) (rationalLocalSpan L p))) :
    rationalLocalGenericBasis L hfg hspan p i = (rationalLocalBasis L hfg p i : E) := by
  rw [rationalLocalGenericBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    rationalLocalGenericEquiv_tmul, one_smul]

/-- Actual local free rank equals the original rational dimension, including rank zero. -/
theorem finrank_rationalLocalSpan (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    Module.finrank (Rᵥ p) (rationalLocalSpan L p) = Module.finrank K E := by
  simpa only [Fintype.card_fin] using
    (Module.finrank_eq_card_basis (rationalLocalGenericBasis L hfg hspan p)).symm

/-- Canonical integral scalars multiply in the actual completed field. -/
instance integralCompletedFieldScalarTower (p : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (Kᵥ p) (Kᵥ p) where
  smul_assoc a x y := by
    change (a • x) * y = a • (x * y)
    exact Algebra.smul_mul_assoc a x y

/-- Canonical integral and completed coefficient-ring scalars agree. -/
instance integralCompletedCoefficientScalarTower (p : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (𝓞ᵥ p) (Kᵥ p) :=
  (S₀).completedLocalRing_integralCompletionScalarTower
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)

/-- The integral action on a completed tensor fibre is induced from its rational scalars. -/
local instance integralCompletedVectorSMul (p : HeightOneSpectrum (𝓞 K)) :
    SMul (𝓞 K) (Kᵥ p ⊗[K] E) where
  smul a x := algebraMap (𝓞 K) K a • x

/-- Integral and completed-field scalars agree on the actual tensor fibre. -/
instance integralCompletedFieldVectorScalarTower (p : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (Kᵥ p) (Kᵥ p ⊗[K] E) :=
  IsScalarTower.of_algebraMap_smul fun a x =>
    (IsScalarTower.algebraMap_smul (Kᵥ p) (algebraMap (𝓞 K) K a) x)

/-- Original integral and completed valuation-ring actions agree on the actual fibre. -/
instance integralCompletedVectorScalarTower (p : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (𝓞ᵥ p) (Kᵥ p ⊗[K] E) :=
  IsScalarTower.of_algebraMap_smul fun a x =>
    (IsScalarTower.algebraMap_smul (Kᵥ p) (algebraMap (𝓞 K) K a) x)

/-- Generic scalar extension identifies the actual completed field tensor of the lattice. -/
def completedGenericEquiv (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    (Kᵥ p) ⊗[𝓞 K] L ≃ₗ[Kᵥ p] Kᵥ p ⊗[K] E :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) K (Kᵥ p) (Kᵥ p) L).symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Kᵥ p) (Kᵥ p))
      (genericTensorEquiv L hspan))

@[simp]
theorem completedGenericEquiv_tmul (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (a : Kᵥ p) (x : L) :
    completedGenericEquiv L hspan p (a ⊗ₜ[𝓞 K] x) = a ⊗ₜ[K] (x : E) := by
  simp [completedGenericEquiv, TensorProduct.AlgebraTensorModule.congr_tmul]

/-- The actual lattice-to-completed-fibre inclusion sends a vector to its literal tensor. -/
def completedInclusion (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    L →ₗ[𝓞 K] Kᵥ p ⊗[K] E :=
  (((TensorProduct.mk K (Kᵥ p) E) 1).restrictScalars (𝓞 K)).comp L.subtype

/-- The literal completed coefficient tensor map of an arbitrary integral lattice. -/
def completedTensorMap (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    (𝓞ᵥ p) ⊗[𝓞 K] L →ₗ[𝓞ᵥ p] Kᵥ p ⊗[K] E := by
  letI := integralCompletedVectorScalarTower (E := E) p
  exact (completedInclusion L p).liftBaseChange (𝓞ᵥ p)

@[simp]
theorem completedTensorMap_tmul (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K))
    (a : 𝓞ᵥ p) (x : L) :
    completedTensorMap L p (a ⊗ₜ[𝓞 K] x) = (a : Kᵥ p) ⊗ₜ[K] (x : E) := by
  rw [completedTensorMap, LinearMap.liftBaseChange_tmul]
  change (a : Kᵥ p) • ((1 : Kᵥ p) ⊗ₜ[K] (x : E)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The literal completed integral lattice, defined as the span of actual rational tensors. -/
def completedSpan (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    Submodule (𝓞ᵥ p) (Kᵥ p ⊗[K] E) :=
  Submodule.span (𝓞ᵥ p) (Set.range fun x : L => (1 : Kᵥ p) ⊗ₜ[K] (x : E))

/-- The image of the canonical completed tensor map is precisely the literal completed span. -/
theorem range_completedTensorMap (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    (completedTensorMap L p).range = completedSpan L p := by
  apply le_antisymm
  · rintro z ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      have hx := (completedSpan L p).smul_mem a
        (Submodule.subset_span (⟨x, rfl⟩ : _ ∈ Set.range _))
      rw [completedTensorMap_tmul]
      change (a : Kᵥ p) • (1 ⊗ₜ[K] (x : E)) ∈ completedSpan L p at hx
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hx
    | add t s ht hs => simpa only [map_add] using (completedSpan L p).add_mem ht hs
  · apply Submodule.span_le.mpr
    rintro z ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ[𝓞 K] x, by rw [completedTensorMap_tmul]; rfl⟩

/-- Actual projectivity makes the canonical completed tensor map injective. -/
theorem completedTensorMap_injective (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (completedTensorMap L p) := by
  let := projective L hfg
  let := integralCompletedCoefficientScalarTower p
  let j : 𝓞ᵥ p →ₗ[𝓞 K] Kᵥ p :=
    (IsScalarTower.toAlgHom (𝓞 K) (𝓞ᵥ p) (Kᵥ p)).toLinearMap
  have hj : Function.Injective j := Subtype.val_injective
  have ht := Module.Flat.rTensor_preserves_injective_linearMap (M := L) j hj
  have heq (t : (𝓞ᵥ p) ⊗[𝓞 K] L) :
      completedGenericEquiv L hspan p (j.rTensor L t) = completedTensorMap L p t := by
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      rw [LinearMap.rTensor_tmul, completedGenericEquiv_tmul, completedTensorMap_tmul]
      rfl
    | add t s ht hs => simp only [map_add, ht, hs]
  intro x y hxy
  apply ht
  apply (completedGenericEquiv L hspan p).injective
  rw [heq, heq]
  exact hxy

/-- Canonical completion of the produced actual rational localization. -/
def completedLocalTensorEquiv (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) :
    (𝓞ᵥ p) ⊗[𝓞 K] L ≃ₗ[𝓞ᵥ p] (𝓞ᵥ p) ⊗[Rᵥ p] rationalLocalSpan L p :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) (Rᵥ p) (𝓞ᵥ p) (𝓞ᵥ p) L).symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (𝓞ᵥ p) (𝓞ᵥ p))
      (rationalLocalTensorEquiv L p))

@[simp]
theorem completedLocalTensorEquiv_tmul (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) (a : 𝓞ᵥ p) (x : L) :
    completedLocalTensorEquiv L p (a ⊗ₜ[𝓞 K] x) = a ⊗ₜ[Rᵥ p] rationalLocalInclusion L p x := by
  simp only [completedLocalTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
  congr 1
  apply Subtype.ext
  change (rationalLocalTensorEquiv L p (1 ⊗ₜ[𝓞 K] x) : E) = (x : E)
  rw [rationalLocalTensorEquiv_tmul]
  simp only [OneMemClass.coe_one, one_smul]

/-- Actual completed tensor map identifies its domain with the literal completed lattice. -/
def completedSpanTensorEquiv (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    (𝓞ᵥ p) ⊗[𝓞 K] L ≃ₗ[𝓞ᵥ p] completedSpan L p :=
  (LinearEquiv.ofInjective (completedTensorMap L p)
    (completedTensorMap_injective L hfg hspan p)).trans
    (LinearEquiv.ofEq _ _ (range_completedTensorMap L p))

@[simp]
theorem completedSpanTensorEquiv_coe (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (t : (𝓞ᵥ p) ⊗[𝓞 K] L) :
    (completedSpanTensorEquiv L hfg hspan p t : Kᵥ p ⊗[K] E) = completedTensorMap L p t := rfl

/-- Produced local bases give an actual finite free basis of the completed integral tensor. -/
def completedTensorBasis (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (p : HeightOneSpectrum (𝓞 K)) :
    Module.Basis (Fin (Module.finrank (Rᵥ p) (rationalLocalSpan L p)))
      (𝓞ᵥ p) ((𝓞ᵥ p) ⊗[𝓞 K] L) :=
  ((rationalLocalBasis L hfg p).baseChange (𝓞ᵥ p)).map (completedLocalTensorEquiv L p).symm

/-- Actual completed lattice basis, derived from the original finite full-spanning lattice. -/
def completedSpanBasis (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    Module.Basis (Fin (Module.finrank (Rᵥ p) (rationalLocalSpan L p)))
      (𝓞ᵥ p) (completedSpan L p) :=
  (completedTensorBasis L hfg p).map (completedSpanTensorEquiv L hfg hspan p)

/-- The literal completed lattice is free, with no freeness certificate supplied. -/
theorem free_completedSpan (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    Module.Free (𝓞ᵥ p) (completedSpan L p) :=
  Module.Free.of_basis (completedSpanBasis L hfg hspan p)

/-- Its literal completed free rank is exactly the original rational dimension. -/
theorem finrank_completedSpan (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    Module.finrank (𝓞ᵥ p) (completedSpan L p) = Module.finrank K E := by
  rw [Module.finrank_eq_card_basis (completedSpanBasis L hfg hspan p), Fintype.card_fin]
  exact finrank_rationalLocalSpan L hfg hspan p

end ArakelovGeometry.NumberFieldFullLattice

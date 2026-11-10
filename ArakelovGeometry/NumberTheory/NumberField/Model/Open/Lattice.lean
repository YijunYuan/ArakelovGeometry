/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Local.Lattice.PrincipalFrame
public import ArakelovGeometry.NumberTheory.NumberField.Model.Open.RegularFunctions
import Mathlib.RingTheory.LocalProperties.Projective

/-!
# Integral descent of actual open models

The original section-ring coefficient maps descend finite open models to
literal integral submodules, with canonical localization reconstruction.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldOpenModel

open NumberFieldOpenRegularFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- Actual local freeness gives projectivity independently of generic or lattice conclusions. -/
theorem projective_of_localizations_free {B M : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] [Module.FinitePresentation B M]
    (hfree : ∀ (I : Ideal B) (_hI : I.IsMaximal),
      Module.Free (Localization.AtPrime I) (LocalizedModule I.primeCompl M)) :
    Module.Projective B M := by
  apply Module.projective_of_localization_maximal
  intro I hI
  let := hI
  let := hfree I hI
  infer_instance

/-- The actual original section map supplies the canonical generic coefficient algebra. -/
abbrev coefficientFieldAlgebra (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) : Algebra (regularFunctions U) K :=
  (regularFunctionsToField U hU).toAlgebra

/-- The actual section-ring action on the original rational vector space. -/
abbrev coefficientModule (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E : Type*) [AddCommGroup E] [Module K E] : Module (regularFunctions U) E :=
  Module.compHom E (regularFunctionsToField U hU)

/-- The actual open action restricts to the original integral action. -/
theorem coefficientScalarTower (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E : Type*) [AddCommGroup E] [Module K E] :
    letI := coefficientModule U hU E
    letI := integralVectorModule (K := K) (E := E)
    IsScalarTower (𝓞 K) (regularFunctions U) E := by
  let := coefficientModule U hU E
  let := integralVectorModule (K := K) (E := E)
  constructor
  intro a b x
  rw [Algebra.smul_def]
  change regularFunctionsToField U hU ((algebraMap (𝓞 K) (regularFunctions U) a) * b) • x =
    (algebraMap (𝓞 K) K a) • (regularFunctionsToField U hU b • x)
  rw [map_mul, regularFunctionsToField_algebraMap, mul_smul]

/-- The actual open action on a rational vector space factors through its canonical field map. -/
theorem coefficientGenericScalarTower
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E : Type*) [AddCommGroup E] [Module K E] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    IsScalarTower (regularFunctions U) K E := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  constructor
  intro a b x
  change (regularFunctionsToField U hU a * b) • x =
    regularFunctionsToField U hU a • (b • x)
  exact mul_smul _ _ _

section Span

variable {A B E : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup E] [Module A E] [Module B E] [IsScalarTower A B E]

/-- The literal inclusion of an integral generating span in the open generating span. -/
def spanInclusion (s : Finset E) :
    Submodule.span A (s : Set E) →ₗ[A] Submodule.span B (s : Set E) :=
  Submodule.inclusion (Submodule.span_le_restrictScalars A B (s : Set E))

/-- Actual clearing of localization denominators reconstructs the open generating span. -/
theorem isLocalizedModule_spanInclusion (S : Submonoid A) [IsLocalization S B]
    (s : Finset E) : IsLocalizedModule S (spanInclusion (B := B) s) := by
  constructor
  · intro t
    rw [← (Algebra.lsmul A (A := B) A (Submodule.span B (s : Set E))).commutes]
    exact (IsLocalization.map_units B t).map _
  · intro y
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S B (s : Set E) y y.property
    refine ⟨(⟨t • (y : E), ht⟩, t), ?_⟩
    rfl
  · intro x y hxy
    refine ⟨1, ?_⟩
    have h : (x : E) = (y : E) :=
      congrArg (fun z : Submodule.span B (s : Set E) => (z : E)) hxy
    simpa only [one_smul] using (Subtype.ext h : x = y)

/-- The canonical actual localization tensor isomorphism of generating spans. -/
def spanBaseChangeEquiv (S : Submonoid A) [IsLocalization S B] (s : Finset E) :
    B ⊗[A] Submodule.span A (s : Set E) ≃ₗ[B] Submodule.span B (s : Set E) := by
  let := isLocalizedModule_spanInclusion (B := B) S s
  exact (IsLocalizedModule.isBaseChange S B (spanInclusion (B := B) s)).equiv

theorem spanBaseChangeEquiv_tmul (S : Submonoid A) [IsLocalization S B]
    (s : Finset E) (b : B) (x : Submodule.span A (s : Set E)) :
    spanBaseChangeEquiv S s (b ⊗ₜ[A] x) = b • spanInclusion (B := B) s x := by
  let := isLocalizedModule_spanInclusion (B := B) S s
  exact (IsLocalizedModule.isBaseChange S B (spanInclusion (B := B) s)).equiv_tmul b x

end Span

/-- Projective modules embed in the scalar extension of a genuinely injective coefficient map. -/
theorem genericTensorInclusion_injective {B F M : Type*} [CommRing B] [Field F]
    [Algebra B F] [AddCommGroup M] [Module B M] [Module.Projective B M]
    (hinj : Function.Injective (algebraMap B F)) :
    Function.Injective ((TensorProduct.mk B F M) 1) := by
  have ht := Module.Flat.rTensor_preserves_injective_linearMap
    (M := M) (Algebra.linearMap B F) hinj
  intro x y hxy
  apply (TensorProduct.lid B M).symm.injective
  apply ht
  simpa only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
    Algebra.linearMap_apply, map_one, TensorProduct.mk_apply] using hxy

/-- The original generic identification maps the actual open model into E. -/
def modelGenericMap (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    (K ⊗[regularFunctions U] M ≃ₗ[K] E) → (M →ₗ[regularFunctions U] E) := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  intro e
  exact (e.restrictScalars (regularFunctions U)).toLinearMap.comp
    ((TensorProduct.mk (regularFunctions U) K M) 1)

/-- The actual source model injects into its original generic vector space. -/
theorem modelGenericMap_injective (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M] [Module.Projective (regularFunctions U) M] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E,
      Function.Injective (modelGenericMap U hU E M e) := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  intro e
  exact e.injective.comp (genericTensorInclusion_injective (regularFunctionsToField_injective U hU))

/-- The literal generic image of the actual open model. -/
def modelGenericImage (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    (K ⊗[regularFunctions U] M ≃ₗ[K] E) → Submodule (regularFunctions U) E := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  intro e
  exact (modelGenericMap U hU E M e).range

/-- Actual finite generation of the model produces finite generation of its genuine image. -/
theorem modelGenericImage_fg (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M] [Module.Finite (regularFunctions U) M] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E, (modelGenericImage U hU E M e).FG := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  intro e
  change (modelGenericMap U hU E M e).range.FG
  simpa only [Submodule.map_top] using
    (Module.Finite.fg_top (R := regularFunctions U) (M := M)).map (modelGenericMap U hU E M e)

/-- The actual generic identification produces full rational span of the literal model image. -/
theorem modelGenericImage_full_span (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E,
      Submodule.span K (modelGenericImage U hU E M e : Set E) = ⊤ := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  intro e
  have hmem : ∀ t : K ⊗[regularFunctions U] M,
      e t ∈ Submodule.span K (modelGenericImage U hU E M e : Set E) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a m =>
      have ht : a ⊗ₜ[regularFunctions U] m =
          a • ((1 : K) ⊗ₜ[regularFunctions U] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, map_smul]
      exact (Submodule.span K (modelGenericImage U hU E M e : Set E)).smul_mem a
        (Submodule.subset_span ⟨m, rfl⟩)
    | add t s ht hs =>
      rw [map_add]
      exact (Submodule.span K (modelGenericImage U hU E M e : Set E)).add_mem ht hs
  apply top_unique
  intro x _
  simpa only [e.apply_symm_apply] using hmem (e.symm x)

/-- A genuine finite actual section-ring submodule has a produced literal integral
descent with canonical tensor reconstruction and equal generic span. -/
theorem exists_integral_descent (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E : Type*) [AddCommGroup E] [Module K E] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientScalarTower U hU E
    ∀ P : Submodule (regularFunctions U) E, P.FG →
      ∃ L : Submodule (𝓞 K) E, L.FG ∧ L ≤ P.restrictScalars (𝓞 K) ∧
        (∃ e : regularFunctions U ⊗[𝓞 K] L ≃ₗ[regularFunctions U] P,
          ∀ (b : regularFunctions U) (x : L),
            (e (b ⊗ₜ[𝓞 K] x) : E) = b • (x : E)) ∧
        Submodule.span K (L : Set E) = Submodule.span K (P : Set E) := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientScalarTower U hU E
  let := coefficientGenericScalarTower U hU E
  let := regularFunctionsLocalization U hU
  intro P hP
  obtain ⟨s, hs⟩ := hP
  subst P
  refine ⟨Submodule.span (𝓞 K) (s : Set E), Submodule.fg_span s.finite_toSet,
    Submodule.span_le_restrictScalars (𝓞 K) (regularFunctions U) (s : Set E), ?_, ?_⟩
  · refine ⟨spanBaseChangeEquiv (Submonoid.powers (openGenerator U hU)) s, ?_⟩
    intro b x
    exact congrArg Subtype.val
      (spanBaseChangeEquiv_tmul (Submonoid.powers (openGenerator U hU)) s b x)
  · rw [Submodule.span_span_of_tower (𝓞 K) K,
      Submodule.span_span_of_tower (regularFunctions U) K]

/-- The original model is canonically identified with its actual generic image. -/
def modelGenericImageEquiv (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M] [Module.Projective (regularFunctions U) M] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E,
      M ≃ₗ[regularFunctions U] modelGenericImage U hU E M e := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  intro e
  exact LinearEquiv.ofInjective (modelGenericMap U hU E M e)
    (modelGenericMap_injective U hU E M e)

theorem modelGenericImageEquiv_apply (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M] [Module.Projective (regularFunctions U) M] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ (e : K ⊗[regularFunctions U] M ≃ₗ[K] E) (m : M),
      (modelGenericImageEquiv U hU E M e m : E) = modelGenericMap U hU E M e m := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  intro e m
  exact LinearEquiv.ofInjective_apply _
    (h := modelGenericMap_injective U hU E M e) _

/-- An original finite projective actual open model has a produced full integral lattice
and canonical reconstruction of the model itself. -/
theorem exists_model_integral_descent (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M]
    [Module.Finite (regularFunctions U) M] [Module.Projective (regularFunctions U) M] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientScalarTower U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E,
      ∃ L : Submodule (𝓞 K) E, L.FG ∧
        L ≤ (modelGenericImage U hU E M e).restrictScalars (𝓞 K) ∧
        Submodule.span K (L : Set E) = ⊤ ∧
        ∃ j : regularFunctions U ⊗[𝓞 K] L ≃ₗ[regularFunctions U] M,
          ∀ (b : regularFunctions U) (x : L),
            modelGenericMap U hU E M e (j (b ⊗ₜ[𝓞 K] x)) = b • (x : E) := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientScalarTower U hU E
  let := coefficientGenericScalarTower U hU E
  intro e
  obtain ⟨L, hfg, hle, ⟨j, hj⟩, hspan⟩ := exists_integral_descent U hU E
    (modelGenericImage U hU E M e) (modelGenericImage_fg U hU E M e)
  refine ⟨L, hfg, hle, hspan.trans (modelGenericImage_full_span U hU E M e),
    j.trans (modelGenericImageEquiv U hU E M e).symm, ?_⟩
  intro b x
  have h := congrArg (fun z : modelGenericImage U hU E M e => (z : E))
    ((modelGenericImageEquiv U hU E M e).apply_symm_apply (j (b ⊗ₜ[𝓞 K] x)))
  rw [modelGenericImageEquiv_apply] at h
  exact h.trans (hj b x)

local notation "S" => AdelicStructure.normalizedNumberFieldAdelicStructure K
local notation "ω" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  ActualPrimeIndexing.normalizedPrimeParameter p
local notation "O" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  AdelicStructure.completedLocalRing (S) (ω p)
    (ActualPrimeIndexing.normalizedPrimeParameter_mem_fin p)
local notation "F" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  AbsoluteValue.Completion (AdelicStructure.ϕ (S) (ω p))

/-- The actual original section map supplies the actual completed coefficient algebra. -/
abbrev completedCoefficientAlgebra (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U) :
    Algebra (regularFunctions U) (O p) := (regularFunctionsToCompleted U hU p hp).toAlgebra

/-- The actual completed coefficient action is compatible with the original generic action. -/
theorem completedCoefficientScalarTower (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E : Type*) [AddCommGroup E] [Module K E]
    (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U) :
    letI := completedCoefficientAlgebra U hU p hp
    letI := coefficientModule U hU (F p ⊗[K] E)
    IsScalarTower (regularFunctions U) (O p) (F p ⊗[K] E) := by
  let := completedCoefficientAlgebra U hU p hp
  let := coefficientModule U hU (F p ⊗[K] E)
  apply IsScalarTower.of_algebraMap_smul
  intro b z
  change (regularFunctionsToCompleted U hU p hp b : F p) • z =
    regularFunctionsToField U hU b • z
  rw [regularFunctionsToCompleted_coe]
  exact IsScalarTower.algebraMap_smul (F p) _ z

/-- The original model's rational vectors map canonically to its actual completed fibre. -/
def completedModelMap (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M] (p : HeightOneSpectrum (𝓞 K)) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    letI := coefficientModule U hU (F p ⊗[K] E)
    (K ⊗[regularFunctions U] M ≃ₗ[K] E) → (M →ₗ[regularFunctions U] F p ⊗[K] E) := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  let := coefficientModule U hU (F p ⊗[K] E)
  let := coefficientGenericScalarTower U hU (F p ⊗[K] E)
  intro e
  exact (((TensorProduct.mk K (F p) E) 1).restrictScalars (regularFunctions U)).comp
    (modelGenericMap U hU E M e)

theorem completedModelMap_apply (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M] (p : HeightOneSpectrum (𝓞 K)) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    letI := coefficientModule U hU (F p ⊗[K] E)
    ∀ (e : K ⊗[regularFunctions U] M ≃ₗ[K] E) (m : M),
      completedModelMap U hU E M p e m = (1 : F p) ⊗ₜ[K] modelGenericMap U hU E M e m := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  let := coefficientModule U hU (F p ⊗[K] E)
  intro e m
  rfl

/-- The actual canonical completed tensor map of the original open model. -/
def completedModelTensorMap (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M]
    (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    letI := coefficientModule U hU (F p ⊗[K] E)
    letI := completedCoefficientAlgebra U hU p hp
    (K ⊗[regularFunctions U] M ≃ₗ[K] E) →
      (O p ⊗[regularFunctions U] M →ₗ[O p] F p ⊗[K] E) := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  let := coefficientModule U hU (F p ⊗[K] E)
  let := completedCoefficientAlgebra U hU p hp
  let := completedCoefficientScalarTower U hU E p hp
  intro e
  exact LinearMap.liftBaseChange (O p) (completedModelMap U hU E M p e)

theorem completedModelTensorMap_tmul (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M]
    (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    letI := coefficientModule U hU (F p ⊗[K] E)
    letI := completedCoefficientAlgebra U hU p hp
    ∀ (e : K ⊗[regularFunctions U] M ≃ₗ[K] E) (a : O p) (m : M),
      completedModelTensorMap U hU E M p hp e (a ⊗ₜ[regularFunctions U] m) =
        (a : F p) ⊗ₜ[K] modelGenericMap U hU E M e m := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  let := coefficientModule U hU (F p ⊗[K] E)
  let := completedCoefficientAlgebra U hU p hp
  intro e a m
  change (a : F p) • ((1 : F p) ⊗ₜ[K] modelGenericMap U hU E M e m) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The literal actual completed span of the original model's generic vectors. -/
def completedModelSpan (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M] (p : HeightOneSpectrum (𝓞 K)) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    (K ⊗[regularFunctions U] M ≃ₗ[K] E) → Submodule (O p) (F p ⊗[K] E) := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  intro e
  exact Submodule.span (O p) (Set.range fun m : M =>
    (1 : F p) ⊗ₜ[K] modelGenericMap U hU E M e m)

/-- The actual completed tensor image is precisely the literal completed model span. -/
theorem range_completedModelTensorMap
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M]
    (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    letI := coefficientModule U hU (F p ⊗[K] E)
    letI := completedCoefficientAlgebra U hU p hp
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E,
      (completedModelTensorMap U hU E M p hp e).range = completedModelSpan U hU E M p e := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  let := coefficientModule U hU (F p ⊗[K] E)
  let := completedCoefficientAlgebra U hU p hp
  intro e
  apply le_antisymm
  · rintro z ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a m =>
      have hm := (completedModelSpan U hU E M p e).smul_mem a
        (Submodule.subset_span (⟨m, rfl⟩ : _ ∈ Set.range _))
      rw [completedModelTensorMap_tmul]
      rw [TensorProduct.smul_tmul'] at hm
      change ((a : F p) * 1) ⊗ₜ[K] modelGenericMap U hU E M e m ∈ _ at hm
      simpa only [mul_one] using hm
    | add t s ht hs => simpa only [map_add] using
        (completedModelSpan U hU E M p e).add_mem ht hs
  · apply Submodule.span_le.mpr
    rintro z ⟨m, rfl⟩
    dsimp only
    refine ⟨1 ⊗ₜ[regularFunctions U] m, ?_⟩
    rw [completedModelTensorMap_tmul]
    rfl

/-- Canonical reconstruction of an actual model preserves its literal completed span. -/
theorem completedModelSpan_eq_integral_of_reconstruction
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M]
    (L : Submodule (𝓞 K) E) (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U) :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ (e : K ⊗[regularFunctions U] M ≃ₗ[K] E)
      (j : regularFunctions U ⊗[𝓞 K] L ≃ₗ[regularFunctions U] M),
      (∀ (b : regularFunctions U) (x : L),
        modelGenericMap U hU E M e (j (b ⊗ₜ[𝓞 K] x)) = b • (x : E)) →
      completedModelSpan U hU E M p e = NumberFieldModel.completedLatticeSpan L p := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientGenericScalarTower U hU E
  intro e j hj
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨m, rfl⟩
    change (1 : F p) ⊗ₜ[K] modelGenericMap U hU E M e m ∈
      NumberFieldModel.completedLatticeSpan L p
    have hmem : ∀ t : regularFunctions U ⊗[𝓞 K] L,
        (1 : F p) ⊗ₜ[K] modelGenericMap U hU E M e (j t) ∈
          NumberFieldModel.completedLatticeSpan L p := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul b x =>
        rw [hj]
        have hm := (NumberFieldModel.completedLatticeSpan L p).smul_mem
          (regularFunctionsToCompleted U hU p hp b)
          (Submodule.subset_span (⟨x, rfl⟩ : _ ∈ Set.range _))
        change (regularFunctionsToCompleted U hU p hp b : F p) •
          ((1 : F p) ⊗ₜ[K] (x : E)) ∈ _ at hm
        rw [regularFunctionsToCompleted_coe] at hm
        rw [IsScalarTower.algebraMap_smul (F p), TensorProduct.smul_tmul'] at hm
        change (1 : F p) ⊗ₜ[K] (regularFunctionsToField U hU b • (x : E)) ∈ _
        rw [TensorProduct.tmul_smul]
        exact hm
      | add t s ht hs =>
        simpa only [map_add, TensorProduct.tmul_add] using
          (NumberFieldModel.completedLatticeSpan L p).add_mem ht hs
    simpa only [j.apply_symm_apply] using hmem (j.symm m)
  · apply Submodule.span_le.mpr
    rintro z ⟨x, rfl⟩
    dsimp only
    have h := hj 1 x
    rw [one_smul] at h
    refine Submodule.subset_span ⟨j (1 ⊗ₜ[𝓞 K] x), ?_⟩
    dsimp only
    rw [h]

/-- The original finite projective model produces a full integral lattice preserving
every actual completed coefficient tensor image on the original open. -/
theorem exists_model_completed_integral_descent
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty)
    (E M : Type*) [AddCommGroup E] [Module K E]
    [AddCommGroup M] [Module (regularFunctions U) M]
    [Module.Finite (regularFunctions U) M] [Module.Projective (regularFunctions U) M] :
    letI := coefficientFieldAlgebra U hU
    letI := coefficientModule U hU E
    letI := coefficientScalarTower U hU E
    letI := coefficientGenericScalarTower U hU E
    ∀ e : K ⊗[regularFunctions U] M ≃ₗ[K] E,
      ∃ L : Submodule (𝓞 K) E, L.FG ∧ Submodule.span K (L : Set E) = ⊤ ∧
        ∃ j : regularFunctions U ⊗[𝓞 K] L ≃ₗ[regularFunctions U] M,
          (∀ (b : regularFunctions U) (x : L),
            modelGenericMap U hU E M e (j (b ⊗ₜ[𝓞 K] x)) = b • (x : E)) ∧
          ∀ (p : HeightOneSpectrum (𝓞 K)) (hp : primePoint p ∈ U),
            letI := coefficientModule U hU (F p ⊗[K] E)
            letI := completedCoefficientAlgebra U hU p hp
            (completedModelTensorMap U hU E M p hp e).range =
              (NumberFieldModel.completedLatticeTensorMap L p).range := by
  let := coefficientFieldAlgebra U hU
  let := coefficientModule U hU E
  let := coefficientScalarTower U hU E
  let := coefficientGenericScalarTower U hU E
  intro e
  obtain ⟨L, hfg, _, hspan, j, hj⟩ := exists_model_integral_descent U hU E M e
  refine ⟨L, hfg, hspan, j, hj, ?_⟩
  intro p hp
  let := coefficientModule U hU (F p ⊗[K] E)
  let := completedCoefficientAlgebra U hU p hp
  rw [range_completedModelTensorMap, NumberFieldModel.range_completedLatticeTensorMap]
  exact completedModelSpan_eq_integral_of_reconstruction U hU E M L p hp e j hj

end ArakelovGeometry.NumberFieldOpenModel

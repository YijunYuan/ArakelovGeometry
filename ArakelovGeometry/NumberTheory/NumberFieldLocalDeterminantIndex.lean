/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.DVRDeterminantIndex
public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldFullLatticeModel

/-!
# The determinant index of an actual localized number-field lattice inclusion
-/

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

namespace ArakelovGeometry.NumberFieldFullLattice

open AdelicStructure ActualPrimeIndexing

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

local notation "localRing" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  AdelicStructure.rationalLocalRing (normalizedNumberFieldAdelicStructure K)
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)

/-- The literal rational coefficient ring at an actual finite prime is a DVR. -/
instance rationalLocalRing_isDiscreteValuationRing (p : HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (localRing p) := by
  change IsDiscreteValuationRing
    ((normalizedNumberFieldAdelicStructure K).rationalLocalRing
      (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p))
  rw [(normalizedNumberFieldAdelicStructure K).rationalLocalRing_eq_finitePlaceInteger
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)
    (FinitePlace.mk p) (NormFamily.normalizedPrimeValue_isEquiv p)]
  infer_instance

/-- Actual integral inclusions give inclusions of the literal local scalar spans. -/
theorem rationalLocalSpan_mono {L₀ L : Submodule (𝓞 K) E} (h : L₀ ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) : rationalLocalSpan L₀ p ≤ rationalLocalSpan L p :=
  Submodule.span_mono h

/-- The localized inclusion preserves the original underlying rational vector. -/
def rationalLocalLatticeInclusion {L₀ L : Submodule (𝓞 K) E} (h : L₀ ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) :
    rationalLocalSpan L₀ p →ₗ[localRing p] rationalLocalSpan L p :=
  Submodule.inclusion (rationalLocalSpan_mono h p)

/-- The literal image of the actual localized inclusion. -/
def rationalLocalLatticeImage {L₀ L : Submodule (𝓞 K) E} (h : L₀ ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) : Submodule (localRing p) (rationalLocalSpan L p) :=
  (rationalLocalLatticeInclusion h p).range

@[simp]
theorem mem_rationalLocalLatticeImage {L₀ L : Submodule (𝓞 K) E} (h : L₀ ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) (x : rationalLocalSpan L p) :
    x ∈ rationalLocalLatticeImage h p ↔ (x : E) ∈ rationalLocalSpan L₀ p := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨(x : E), hx⟩, rfl⟩

/-- Injectivity is inherited from equality of actual underlying rational vectors. -/
theorem rationalLocalLatticeInclusion_injective {L₀ L : Submodule (𝓞 K) E} (h : L₀ ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) : Function.Injective (rationalLocalLatticeInclusion h p) :=
  Submodule.inclusion_injective _

/-- The produced local basis reindexed by the original rational dimension. -/
def rationalLocalBasisFinrank (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    Module.Basis (Fin (Module.finrank K E)) (localRing p) (rationalLocalSpan L p) :=
  (rationalLocalBasis L hfg p).reindex (finCongr (finrank_rationalLocalSpan L hfg hspan p))

/-- The actual injection identifies the smaller local lattice with its literal image. -/
def rationalLocalLatticeImageEquiv {L₀ L : Submodule (𝓞 K) E} (h : L₀ ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) :
    rationalLocalSpan L₀ p ≃ₗ[localRing p] rationalLocalLatticeImage h p :=
  LinearEquiv.ofInjective (rationalLocalLatticeInclusion h p)
    (rationalLocalLatticeInclusion_injective h p)

@[simp]
theorem rationalLocalLatticeImageEquiv_coe {L₀ L : Submodule (𝓞 K) E} (h : L₀ ≤ L)
    (p : HeightOneSpectrum (𝓞 K)) (x : rationalLocalSpan L₀ p) :
    (rationalLocalLatticeImageEquiv h p x : rationalLocalSpan L p) =
      rationalLocalLatticeInclusion h p x := rfl

/-- Quotient length of the actual localized inclusion is its determinant valuation
in bases produced solely from finite generation and full rational span. -/
theorem rationalLocalLattice_length_eq_addVal_det
    (L₀ L : Submodule (𝓞 K) E) (h : L₀ ≤ L) (hfg₀ : L₀.FG) (hfg : L.FG)
    (hspan₀ : Submodule.span K (L₀ : Set E) = ⊤)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    Module.length (localRing p) (rationalLocalSpan L p ⧸ rationalLocalLatticeImage h p) =
      IsDiscreteValuationRing.addVal (localRing p)
        (LinearMap.toMatrix (rationalLocalBasisFinrank L₀ hfg₀ hspan₀ p)
          (rationalLocalBasisFinrank L hfg hspan p) (rationalLocalLatticeInclusion h p)).det := by
  let b := rationalLocalBasisFinrank L hfg hspan p
  let c := rationalLocalBasisFinrank L₀ hfg₀ hspan₀ p
  have hlen := DVRDeterminantIndex.length_quotient_eq_addVal_det
    (rationalLocalLatticeImage h p) b (c.map (rationalLocalLatticeImageEquiv h p))
  have hmat : LinearMap.toMatrix (c.map (rationalLocalLatticeImageEquiv h p)) b
      (rationalLocalLatticeImage h p).subtype =
      LinearMap.toMatrix c b (rationalLocalLatticeInclusion h p) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Module.Basis.map_apply,
      rationalLocalLatticeImageEquiv_coe, Submodule.subtype_apply]
  exact hlen.trans (congrArg (fun A => IsDiscreteValuationRing.addVal (localRing p) A.det) hmat)

end ArakelovGeometry.NumberFieldFullLattice

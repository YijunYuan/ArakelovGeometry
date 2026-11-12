/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Full.Model
public import ArakelovGeometry.NumberTheory.NumberField.Local.Lattice.PrincipalFrame

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Model
import Mathlib.Topology.Sheaves.Init

/-!
# Actual gauges of arbitrary full number-field lattices

Produced rational local bases identify the literal completed tensor image
with its coordinate lattice at every finite place. The intrinsic scalar
infimum is its separating basis norm. Retaining arbitrary infinite norms
then gives a genuinely coherent dominated family, including its actual dual.
The global rational ball and associated sheaf are separate obligations.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct
noncomputable section

namespace ArakelovGeometry.NumberFieldFullLattice

open AdelicStructure ActualPrimeIndexing
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

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

/-- The full-lattice span is the already canonical actual completed lattice span. -/
theorem completedSpan_eq_canonical (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) :
    completedSpan L p = NumberFieldModel.completedLatticeSpan L p := rfl

/-- The literal completed tensor map is the already canonical actual model tensor map. -/
theorem completedTensorMap_eq_canonical (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) :
    completedTensorMap L p = NumberFieldModel.completedLatticeTensorMap L p := by
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    rw [completedTensorMap_tmul, NumberFieldModel.completedLatticeTensorMap_tmul]
  | add t s ht hs => simp only [map_add, ht, hs]

/-- The rational local ring acts through its embedding into the original scalar field. -/
local instance completedRationalVectorSMul (p : HeightOneSpectrum (𝓞 K)) :
    SMul (Rᵥ p) (Kᵥ p ⊗[K] E) where
  smul a x := (a : K) • x

/-- The rational local and completed local scalar actions agree on completed vectors. -/
theorem completedRationalVectorScalarTower (p : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (Rᵥ p) (𝓞ᵥ p) (Kᵥ p ⊗[K] E) :=
  IsScalarTower.of_algebraMap_smul fun a x =>
    (IsScalarTower.algebraMap_smul (Kᵥ p) (a : K) x)

/-- The actual completed map from the produced literal rational local span. -/
def completedRationalTensorMap (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) :
    (𝓞ᵥ p) ⊗[Rᵥ p] rationalLocalSpan L p →ₗ[𝓞ᵥ p] Kᵥ p ⊗[K] E := by
  letI := completedRationalVectorScalarTower (E := E) p
  let q := (((TensorProduct.mk K (Kᵥ p) E) (1 : Kᵥ p)).restrictScalars (Rᵥ p)).comp
    (rationalLocalSpan L p).subtype
  exact q.liftBaseChange (𝓞ᵥ p)

@[simp]
theorem completedRationalTensorMap_tmul (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) (a : 𝓞ᵥ p) (x : rationalLocalSpan L p) :
    completedRationalTensorMap L p (a ⊗ₜ[Rᵥ p] x) = (a : Kᵥ p) ⊗ₜ[K] (x : E) := by
  rw [completedRationalTensorMap, LinearMap.liftBaseChange_tmul]
  change (a : Kᵥ p) • ((1 : Kᵥ p) ⊗ₜ[K] (x : E)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Both literal completed tensor constructions commute with actual rational localization. -/
theorem completedRationalTensorMap_localTensorEquiv (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K)) (t : (𝓞ᵥ p) ⊗[𝓞 K] L) :
    completedRationalTensorMap L p (completedLocalTensorEquiv L p t) =
      completedTensorMap L p t := by
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    rw [completedLocalTensorEquiv_tmul, completedRationalTensorMap_tmul,
      completedTensorMap_tmul]
    rfl
  | add t s ht hs => simp only [map_add, ht, hs]

/-- The produced completed integral basis consists of literal rational local-basis tensors. -/
theorem completedSpanBasis_coe (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (i : Fin (Module.finrank (Rᵥ p) (rationalLocalSpan L p))) :
    (completedSpanBasis L hfg hspan p i : Kᵥ p ⊗[K] E) =
      (1 : Kᵥ p) ⊗ₜ[K] (rationalLocalBasis L hfg p i : E) := by
  rw [completedSpanBasis, Module.Basis.map_apply, completedSpanTensorEquiv_coe,
    ← completedRationalTensorMap_localTensorEquiv, completedTensorBasis,
    Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.baseChange_apply,
    completedRationalTensorMap_tmul]
  rfl

/-- The literal canonical completed lattice is the produced actual coordinate lattice. -/
theorem completedLatticeSpan_eq_localBasis (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K)) :
    NumberFieldModel.completedLatticeSpan L p = NormFamily.completedBasisLattice
      (S₀) (rationalLocalGenericBasis L hfg hspan p) (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p) := by
  rw [← completedSpan_eq_canonical]
  let M := completedSpan L p
  let b := completedSpanBasis L hfg hspan p
  have hs := congrArg (Submodule.map M.subtype) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hs
  dsimp only [M] at hs
  rw [NormFamily.completedBasisLattice_eq_span, ← hs]
  apply congrArg (Submodule.span (𝓞ᵥ p))
  rw [← Set.range_comp]
  apply congrArg Set.range
  funext i
  change (completedSpanBasis L hfg hspan p i : Kᵥ p ⊗[K] E) = _
  rw [completedSpanBasis_coe, rationalLocalGenericBasis_coe]

/-- Its genuine scalar-infimum gauge is the produced basis norm on the actual fibre. -/
theorem scalarLatticeGauge_eq_localBasisNorm (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (z : Kᵥ p ⊗[K] E) :
    scalarLatticeGauge (F := Kᵥ p) (NumberFieldModel.completedLatticeSpan L p : Set _) z =
      (NormFamily.ofBasis (S₀) E (rationalLocalGenericBasis L hfg hspan p)).norm
        (normalizedPrimeParameter p) z := by
  rw [completedLatticeSpan_eq_localBasis L hfg hspan p]
  exact NormFamily.scalarLatticeGauge_completedBasisLattice _ _
    (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm
        (normalizedPrimeParameter p))) z

/-- The actual gauge's unit ball is the literal completed lattice. -/
theorem scalarLatticeGauge_le_one_iff_completedLatticeSpan
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (z : Kᵥ p ⊗[K] E) :
    scalarLatticeGauge (F := Kᵥ p) (NumberFieldModel.completedLatticeSpan L p : Set _) z ≤ 1 ↔
      z ∈ NumberFieldModel.completedLatticeSpan L p := by
  rw [completedLatticeSpan_eq_localBasis L hfg hspan p]
  exact NormFamily.scalarLatticeGauge_completedBasisLattice_le_one_iff _ _
    (normalizedPrimeParameter_mem_fin p)
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm
        (normalizedPrimeParameter p))) z

/-- Separation of the literal scalar-infimum gauge, including the zero-rank case. -/
theorem scalarLatticeGauge_eq_zero_iff (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (z : Kᵥ p ⊗[K] E) :
    scalarLatticeGauge (F := Kᵥ p) (NumberFieldModel.completedLatticeSpan L p : Set _) z = 0 ↔
      z = 0 := by
  rw [scalarLatticeGauge_eq_localBasisNorm L hfg hspan p]
  exact (NormFamily.ofBasis _ E _).norm_eq_zero_iff _ z

/-- Literal completed scalar compatibility of the actual arbitrary full-lattice gauge. -/
theorem scalarLatticeGauge_smul (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (a : Kᵥ p) (z : Kᵥ p ⊗[K] E) :
    scalarLatticeGauge (F := Kᵥ p) (NumberFieldModel.completedLatticeSpan L p : Set _) (a • z) =
      ‖a‖ * scalarLatticeGauge (F := Kᵥ p)
        (NumberFieldModel.completedLatticeSpan L p : Set _) z := by
  simp only [scalarLatticeGauge_eq_localBasisNorm L hfg hspan p, NormFamily.norm_smul]

/-- Literal finite-place ultrametric inequality for the actual scalar-infimum gauge. -/
theorem scalarLatticeGauge_add_le_max (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (x y : Kᵥ p ⊗[K] E) :
    scalarLatticeGauge (F := Kᵥ p) (NumberFieldModel.completedLatticeSpan L p : Set _) (x + y) ≤
      max (scalarLatticeGauge (F := Kᵥ p) (NumberFieldModel.completedLatticeSpan L p : Set _) x)
        (scalarLatticeGauge (F := Kᵥ p) (NumberFieldModel.completedLatticeSpan L p : Set _) y) := by
  let b := rationalLocalGenericBasis L hfg hspan p
  have h := NormFamily.ofBasisMixed_isUltrametric b _
    (normalizedPrimeParameter_mem_fin p) x y
  rw [NormFamily.ofBasisMixed_norm_of_finite b _ (normalizedPrimeParameter_mem_fin p),
    NormFamily.ofBasisMixed_norm_of_finite b _ (normalizedPrimeParameter_mem_fin p),
    NormFamily.ofBasisMixed_norm_of_finite b _ (normalizedPrimeParameter_mem_fin p)] at h
  simpa only [scalarLatticeGauge_eq_localBasisNorm L hfg hspan p] using h

/-- The prime ideal corresponding to a finite normalized place. -/
def primeAt (ω : (S₀).Ω) (hω : ω ∈ (S₀).Ωfin) :
    HeightOneSpectrum (𝓞 K) := (exists_normalizedPrimeParameter_eq ω hω).choose

private theorem primeAt_parameter (p : HeightOneSpectrum (𝓞 K)) :
    primeAt (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) = p :=
  normalizedPrimeParameter_injective
    (exists_normalizedPrimeParameter_eq (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p)).choose_spec

/-- Actual completed finite lattice gauges, with arbitrary given infinite norms retained. -/
def fullLatticeGaugeFamily (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (S₀) E) :
    NormFamily (S₀) E where
  norm ω := if hω : ω ∈ (S₀).Ωfin then
    (NormFamily.ofBasis (S₀) E
      (rationalLocalGenericBasis L hfg hspan (primeAt ω hω))).norm ω
    else η.norm ω
  norm_eq_zero_iff ω z := by
    split
    · exact (NormFamily.ofBasis _ E _).norm_eq_zero_iff ω z
    · exact η.norm_eq_zero_iff ω z

/-- At every actual finite place the constructed norm is the literal lattice scalar gauge. -/
theorem fullLatticeGaugeFamily_norm_prime (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (S₀) E)
    (p : HeightOneSpectrum (𝓞 K)) (z : Kᵥ p ⊗[K] E) :
    (fullLatticeGaugeFamily L hfg hspan η).norm (normalizedPrimeParameter p) z =
      scalarLatticeGauge (F := Kᵥ p) (NumberFieldModel.completedLatticeSpan L p : Set _) z := by
  dsimp only [fullLatticeGaugeFamily]
  rw [dite_eq_left (normalizedPrimeParameter_mem_fin p), primeAt_parameter]
  exact (scalarLatticeGauge_eq_localBasisNorm L hfg hspan p z).symm

/-- The given infinite completed norms are retained literally, without a domination premise. -/
theorem fullLatticeGaugeFamily_norm_not_finite (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (S₀) E)
    (ω : (S₀).Ω) (hω : ω ∉ (S₀).Ωfin) :
    (fullLatticeGaugeFamily L hfg hspan η).norm ω = η.norm ω := by
  change (if hω : ω ∈ (S₀).Ωfin then _ else _) = _
  rw [dite_eq_right hω]

/-- The family is genuinely ultrametric at every finite completed fibre. -/
instance fullLatticeGaugeFamily_isUltrametric (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (S₀) E) :
    (fullLatticeGaugeFamily L hfg hspan η).IsUltrametric := by
  constructor
  intro ω hω x y
  let b := rationalLocalGenericBasis L hfg hspan (primeAt ω hω)
  have hn (z) : (fullLatticeGaugeFamily L hfg hspan η).norm ω z =
      (NormFamily.ofBasisMixed (S₀) E b).norm ω z := by
    rw [NormFamily.ofBasisMixed_norm_of_finite b ω hω]
    dsimp only [fullLatticeGaugeFamily]
    rw [dite_eq_left hω]
  simp only [hn]
  exact NormFamily.ofBasisMixed_isUltrametric b ω hω x y

/-- Its literal completed finite unit ball is the canonical completed tensor image. -/
theorem fullLatticeGaugeFamily_completedUnitBall_eq
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (S₀) E)
    (p : HeightOneSpectrum (𝓞 K)) :
    (fullLatticeGaugeFamily L hfg hspan η).completedUnitBall (normalizedPrimeParameter p) =
      (NumberFieldModel.completedLatticeSpan L p : Set (Kᵥ p ⊗[K] E)) := by
  ext z
  change (fullLatticeGaugeFamily L hfg hspan η).norm (normalizedPrimeParameter p) z ≤ 1 ↔ _
  rw [fullLatticeGaugeFamily_norm_prime]
  exact scalarLatticeGauge_le_one_iff_completedLatticeSpan L hfg hspan p z

/-- Literal FG/full span supplies a common actual gauge basis outside finitely many primes. -/
theorem fullLatticeGaugeFamily_exists_common_basis
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (S₀) E)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ p ∉ T, ∀ z : Kᵥ p ⊗[K] E,
      (fullLatticeGaugeFamily L hfg hspan η).norm (normalizedPrimeParameter p) z =
        (NormFamily.ofBasis (S₀) E b).norm (normalizedPrimeParameter p) z := by
  classical
  obtain ⟨f, hf, hfin, hframe⟩ :=
    NumberFieldModel.exists_completed_lattice_gauge_frame L hfg hspan b
  refine ⟨hfin.toFinset, ?_⟩
  intro p hp z
  rw [fullLatticeGaugeFamily_norm_prime]
  exact hframe p (by simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hp) z

variable [FiniteDimensional K E]

/-- Source coherence and both primal/actual-dual domination are produced for arbitrary L. -/
theorem fullLatticeGaugeFamily_coherent_and_dominated
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (S₀) E) :
    (fullLatticeGaugeFamily L hfg hspan η).HasFiniteNormExceptions ∧
      (fullLatticeGaugeFamily L hfg hspan η).IsDominated := by
  let b := Module.finBasis K E
  obtain ⟨T, hT⟩ := fullLatticeGaugeFamily_exists_common_basis L hfg hspan η b
  exact NormFamily.coherent_and_dominated_of_basisGauge_eq_off_finite_primes
    (fullLatticeGaugeFamily L hfg hspan η) b T hT

end ArakelovGeometry.NumberFieldFullLattice

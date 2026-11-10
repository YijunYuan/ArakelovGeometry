/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldInvertibleGenericFibre
import ArakelovGeometry.NumberTheory.NumberFieldDegreeCovolume

/-!
# Original finite projective modules in their literal generic images

The existing canonical generic inclusion and generic image are reused in every
rank. Their original completed tensors and diagonal images are identified with
the actual full-lattice objects in the same generic vector space.
-/

noncomputable section
open NumberField IsDedekindDomain TensorProduct
open scoped NumberField TensorProduct

namespace ArakelovGeometry.NumberFieldProjectiveGeneric

open AdelicStructure ActualPrimeIndexing NumberFieldInvertibleGeneric
  NumberFieldArchimedeanVectorDiagonal
attribute [local instance 2000] integralVectorModule
attribute [local instance] normalizedNumberFieldAdelicStructure_isProper

variable {K : Type*} [Field K] [NumberField K]
  (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

/-- Projectivity makes the existing canonical generic tensor inclusion injective. -/
theorem genericInclusion_injective [Module.Projective (𝓞 K) M] :
    Function.Injective (genericInclusion (K := K) M) :=
  NumberFieldOpenModel.genericTensorInclusion_injective (IsFractionRing.injective (𝓞 K) K)

/-- The original projective module identifies canonically with its existing literal image. -/
def genericImageEquiv [Module.Projective (𝓞 K) M] :
    M ≃ₗ[𝓞 K] genericImage (K := K) M :=
  LinearEquiv.ofInjective (genericInclusion (K := K) M)
    (genericInclusion_injective (K := K) M)

@[simp]
theorem genericImageEquiv_coe [Module.Projective (𝓞 K) M] (m : M) :
    (genericImageEquiv (K := K) M m : K ⊗[𝓞 K] M) =
      genericInclusion (K := K) M m := rfl

omit [NumberField K] in
/-- Original finite generation produces finite generation of the exact existing image. -/
theorem genericImage_fg [Module.Finite (𝓞 K) M] : (genericImage (K := K) M).FG := by
  rw [genericImage, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

omit [NumberField K] in
/-- Finite generation gives finite-dimensionality of the actual generic tensor fibre. -/
theorem genericFiniteDimensional [Module.Finite (𝓞 K) M] :
    FiniteDimensional K (K ⊗[𝓞 K] M) := Module.Finite.base_change (𝓞 K) K M

private abbrev F (p : HeightOneSpectrum (𝓞 K)) :=
  ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).Completion
private abbrev O (p : HeightOneSpectrum (𝓞 K)) :=
  (normalizedNumberFieldAdelicStructure K).completedLocalRing (normalizedPrimeParameter p)
    (normalizedPrimeParameter_mem_fin p)

/-- The original completed map is scalar extension of the actual original generic inclusion. -/
def completedTensorMap (p : HeightOneSpectrum (𝓞 K)) :
    O p ⊗[𝓞 K] M →ₗ[O p] F p ⊗[K] (K ⊗[𝓞 K] M) :=
  @LinearMap.liftBaseChange (𝓞 K) M (F p ⊗[K] (K ⊗[𝓞 K] M)) (O p) _ _ _ _ _ _
    (integralVectorModule (K := K)) _
    (NumberFieldModel.completedVector_integralScalarTower p)
    ((NumberFieldModel.completedVectorMap p).comp (genericInclusion (K := K) M))

/-- The completed map sends the original pure tensor to the prescribed completed vector. -/
@[simp]
theorem completedTensorMap_tmul (p : HeightOneSpectrum (𝓞 K)) (a : O p) (m : M) :
    completedTensorMap (K := K) M p (a ⊗ₜ[𝓞 K] m) =
      (a : F p) ⊗ₜ[K] (genericInclusion (K := K) M m) := by
  change (a : F p) • ((1 : F p) ⊗ₜ[K] (genericInclusion (K := K) M m)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The original map commutes with the canonical base change of the original image isomorphism. -/
theorem completedTensorMap_eq_latticeMap [Module.Projective (𝓞 K) M]
    (p : HeightOneSpectrum (𝓞 K)) :
    completedTensorMap (K := K) M p =
      (NumberFieldModel.completedLatticeTensorMap (genericImage (K := K) M) p).comp
        (LinearEquiv.baseChange (𝓞 K) (O p) M (genericImage (K := K) M)
          (genericImageEquiv (K := K) M)).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro a m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_baseChange, LinearMap.baseChange_tmul,
    NumberFieldModel.completedLatticeTensorMap_tmul, completedTensorMap_tmul]
  rfl

/-- The actual original completed image is the canonical full-lattice completed span. -/
theorem completedTensorMap_range [Module.Projective (𝓞 K) M]
    (p : HeightOneSpectrum (𝓞 K)) :
    (completedTensorMap (K := K) M p).range =
      NumberFieldModel.completedLatticeSpan (genericImage (K := K) M) p := by
  rw [completedTensorMap_eq_latticeMap, LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.baseChange (𝓞 K) (O p) M (genericImage (K := K) M)
      (genericImageEquiv (K := K) M)).range]
  exact NumberFieldModel.range_completedLatticeTensorMap _ _

/-- The original completed tensor map is injective for every finite projective module. -/
theorem completedTensorMap_injective [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    (p : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (completedTensorMap (K := K) M p) := by
  rw [completedTensorMap_eq_latticeMap]
  have hi := NumberFieldFullLattice.completedTensorMap_injective
    (genericImage (K := K) M) (genericImage_fg (K := K) M)
    (genericImage_fullSpan (K := K) M) p
  rw [NumberFieldFullLattice.completedTensorMap_eq_canonical] at hi
  exact hi.comp
    (LinearEquiv.baseChange (𝓞 K) (O p) M (genericImage (K := K) M)
      (genericImageEquiv (K := K) M)).injective

/-- The canonical full-lattice finite norm is exactly the gauge of the original
module's completed tensor image in the same actual completed generic fibre. -/
theorem fullLatticeGaugeFamily_norm_originalCompletedImage
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (p : HeightOneSpectrum (𝓞 K)) (z : F p ⊗[K] (K ⊗[𝓞 K] M)) :
    (NumberFieldFullLattice.fullLatticeGaugeFamily (genericImage (K := K) M)
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η).norm
        (normalizedPrimeParameter p) z =
      scalarLatticeGauge (F := F p) ((completedTensorMap (K := K) M p).range : Set _) z := by
  rw [NumberFieldFullLattice.fullLatticeGaugeFamily_norm_prime, completedTensorMap_range]

/-- The prescribed original infinite norms are retained on the same actual generic fibre. -/
theorem fullLatticeGaugeFamily_norm_not_finite [Module.Finite (𝓞 K) M]
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∉ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] (K ⊗[𝓞 K] M)) :
    (NumberFieldFullLattice.fullLatticeGaugeFamily (genericImage (K := K) M)
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η).norm ω z = η.norm ω z :=
  by rw [NumberFieldFullLattice.fullLatticeGaugeFamily_norm_not_finite _ _ _ _ ω hω]

/-- The literal diagonal of the original abstract module in the actual completed product. -/
def originalDiagonalMap : M →ₗ[ℤ] CompletedVectorProduct K (K ⊗[𝓞 K] M) :=
  (vectorDiagonalMap (K := K) (E := K ⊗[𝓞 K] M)).restrictScalars ℤ |>.comp
    ((genericInclusion (K := K) M).restrictScalars ℤ)

@[simp]
theorem originalDiagonalMap_apply (m : M) (w : InfinitePlace K) :
    originalDiagonalMap (K := K) M m w =
      (1 : CompletedCoefficient w) ⊗ₜ[K] (genericInclusion (K := K) M m) := rfl

/-- The original diagonal map is injective, so it records the original module faithfully. -/
theorem originalDiagonalMap_injective [Module.Projective (𝓞 K) M] :
    Function.Injective (originalDiagonalMap (K := K) M) :=
  NumberFieldArchimedeanCovolume.vectorDiagonalMap_injective.comp
    (genericInclusion_injective (K := K) M)

/-- The original diagonal commutes with the literal image isomorphism. -/
theorem originalDiagonalMap_eq_latticeDiagonalMap [Module.Projective (𝓞 K) M] :
    originalDiagonalMap (K := K) M =
      (latticeDiagonalMap (genericImage (K := K) M)).comp
        ((genericImageEquiv (K := K) M).restrictScalars ℤ).toLinearMap := by
  ext m
  rfl

/-- The original module has exactly the canonical full-lattice diagonal image,
as equal submodules of the very same normed completed product. -/
theorem originalDiagonalMap_range [Module.Projective (𝓞 K) M] :
    (originalDiagonalMap (K := K) M).range = diagonalLattice (genericImage (K := K) M) := by
  rw [originalDiagonalMap_eq_latticeDiagonalMap,
    ((genericImageEquiv (K := K) M).restrictScalars ℤ).range_comp]
  rfl

/-- The actual original diagonal is discrete in the existing Euclidean product metric. -/
theorem originalDiagonalMap_range_discrete
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    letI := genericFiniteDimensional (K := K) M
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup η
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedSpace η
    DiscreteTopology (originalDiagonalMap (K := K) M).range := by
  let := genericFiniteDimensional (K := K) M
  let := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup η
  let := NumberFieldArchimedeanEuclidean.euclideanNormedSpace η
  rw [originalDiagonalMap_range]
  exact NumberFieldArchimedeanEuclidean.euclidean_discrete_diagonalLattice η _
    (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M)

/-- The original module diagonal is a full integer lattice for the prescribed
Archimedean product metric, using the existing Euclidean structure. -/
theorem originalDiagonalMap_range_isZLattice
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    letI := genericFiniteDimensional (K := K) M
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup η
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedSpace η
    letI := originalDiagonalMap_range_discrete (K := K) M η
    IsZLattice ℝ (originalDiagonalMap (K := K) M).range := by
  let := genericFiniteDimensional (K := K) M
  let := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup η
  let := NumberFieldArchimedeanEuclidean.euclideanNormedSpace η
  let := originalDiagonalMap_range_discrete (K := K) M η
  simpa only [originalDiagonalMap_range] using
    NumberFieldArchimedeanEuclidean.euclidean_isZLattice_diagonalLattice η _
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M)

/-- The actual covolume of the original abstract module diagonal satisfies the
accepted degree formula. The lattice, norms and measure are the existing ones. -/
theorem originalDiagonal_covolume_eq_exp_neg_degree
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := genericFiniteDimensional (K := K) M
    let L := genericImage (K := K) M
    let hfg := genericImage_fg (K := K) M
    let hspan := genericImage_fullSpan (K := K) M
    let ξ := NumberFieldFullLattice.fullLatticeGaugeFamily L hfg hspan η
    let hξ := NumberFieldFullLattice.fullLatticeGaugeFamily_isHermitian L hfg hspan η hη
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup ξ
    letI := NumberFieldArchimedeanEuclidean.euclideanNormedSpace ξ
    letI := NumberFieldArchimedeanEuclidean.euclideanInnerProduct hξ
    letI : MeasurableSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := borel _
    letI : BorelSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace
      (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
    ZLattice.covolume (originalDiagonalMap (K := K) M).range =
      Real.exp (-(NumberFieldFullLattice.fullLatticeAdelicBundle L hfg hspan η).degree
        (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions +
        (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * Real.log
          ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
            Real.sqrt |(NumberField.discr K : ℝ)|)) := by
  let := genericFiniteDimensional (K := K) M
  let L := genericImage (K := K) M
  let hfg := genericImage_fg (K := K) M
  let hspan := genericImage_fullSpan (K := K) M
  let ξ := NumberFieldFullLattice.fullLatticeGaugeFamily L hfg hspan η
  let hξ := NumberFieldFullLattice.fullLatticeGaugeFamily_isHermitian L hfg hspan η hη
  let := NumberFieldArchimedeanEuclidean.euclideanNormedAddCommGroup ξ
  let := NumberFieldArchimedeanEuclidean.euclideanNormedSpace ξ
  let := NumberFieldArchimedeanEuclidean.euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := borel _
  let : BorelSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
  rw [originalDiagonalMap_range]
  exact NumberFieldFullLattice.fullLattice_euclideanCovolume_eq_exp_neg_degree L hfg hspan η hη

end ArakelovGeometry.NumberFieldProjectiveGeneric

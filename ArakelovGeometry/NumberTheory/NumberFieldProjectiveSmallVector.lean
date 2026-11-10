/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldProjectiveGenericFibre
import ArakelovGeometry.NumberTheory.NumberFieldArithmeticSmallVector

/-! # The arithmetic large-degree bound on the original finite projective module -/

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldProjectiveGeneric

open AdelicStructure NumberFieldInvertibleGeneric NumberFieldFullLattice
  NumberFieldArchimedeanVectorDiagonal

attribute [local instance] normalizedNumberFieldAdelicStructure_isProper

variable {K : Type*} [Field K] [NumberField K]
  (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

/-- The actual source large-degree vector belongs to the original projective module.
Its degree is measured in the same original generic fibre with the prescribed infinite
norms and the original completed-image gauges at finite places. -/
theorem exists_original_nonzero_large_degree
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (hn : 0 < Module.finrank K (K ⊗[𝓞 K] M)) :
    letI := genericFiniteDimensional (K := K) M
    let V := fullLatticeAdelicBundle (genericImage (K := K) M)
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η
    ∃ m : M, ∃ hm : genericInclusion (K := K) M m ≠ 0, m ≠ 0 ∧
      V.slope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
        (Module.finrank ℚ K : ℝ) / 2 * Real.log (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) -
          Real.log |(NumberField.discr K : ℝ)| / 2 ≤
            V.toNormFamily.vectorDegree V.isDominated V.isMeasurable
              ⟨genericInclusion (K := K) M m, hm⟩ := by
  let := genericFiniteDimensional (K := K) M
  obtain ⟨s, hs, hd⟩ := NumberFieldArithmeticSmallVector.exists_integral_nonzero_large_degree
    (genericImage (K := K) M) (genericImage_fg (K := K) M)
    (genericImage_fullSpan (K := K) M) η hη hn
  obtain ⟨m, hm⟩ := (genericImageEquiv (K := K) M).surjective ⟨s.val, hs⟩
  have he : genericInclusion (K := K) M m = s.val :=
    congrArg Subtype.val hm
  have hm' : genericInclusion (K := K) M m ≠ 0 := by
    rw [he]
    exact s.property
  refine ⟨m, hm', ?_, ?_⟩
  · intro hzero
    apply hm'
    rw [hzero, map_zero]
  · simpa only [he] using hd

/-- The original diagonal covolume with the source constant written explicitly. -/
theorem originalDiagonal_covolume_eq_exp_neg_degree_sub_chi
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
        (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
        (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) *
          ((InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 -
            Real.log |(NumberField.discr K : ℝ)| / 2)) := by
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
  dsimp only
  rw [originalDiagonal_covolume_eq_exp_neg_degree (K := K) M η hη,
    NumberFieldMinkowskiRadius.log_covolume_constant]
  congr 1
  ring

end ArakelovGeometry.NumberFieldProjectiveGeneric

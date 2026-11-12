/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Model.Sections
public import ArakelovGeometry.NumberTheory.NumberField.Model.TraceDual.Metric
public import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.ComparisonConstants

import ArakelovGeometry.AdelicCurve.Equiv
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.NumberTheory.NumberField.Minima.ProjectiveSmallVector
import ArakelovGeometry.NumberTheory.NumberField.Minkowski.SectionCount
import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.CountComparison
import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.DualCountComparison
import Mathlib.Topology.Sheaves.Init

/-! # Actual arithmetic covolume and classical duality -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldClassicalArithmeticDuality

open AdelicStructure NumberFieldProjectiveGeneric NumberFieldFullLattice
  NumberFieldArchimedeanCovolume NumberFieldArchimedeanEuclidean
  NumberFieldArchimedeanVectorDiagonal NumberFieldCodifferentDual
  NumberFieldProjectiveTraceDualGeneric NumberFieldClassicalTraceDual
  NumberFieldClassicalTraceDualMetric NumberFieldClassicalDualCountComparison
  NumberFieldClassicalCountComparison NumberFieldClassicalComparisonConstants
open NumberFieldInvertibleGeneric (genericImage genericImage_fullSpan)

attribute [local instance] traceTensor_finite traceTensor_projective

universe u
variable {K : Type u} [Field K] [NumberField K]
  (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- The actual canonical arithmetic metric converts logarithmic Euclidean
covolume to actual determinant degree with the signed source constant. -/
theorem log_euclideanCovolume_fullLatticeGaugeFamily
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    let L := genericImage (K := K) M
    let hfg := genericImage_fg (K := K) M
    let hspan := genericImage_fullSpan (K := K) M
    let ξ := fullLatticeGaugeFamily L hfg hspan η
    let hξ : ξ.IsHermitian :=
      fullLatticeGaugeFamily_isHermitian L hfg hspan η
    let V := fullLatticeAdelicBundle L hfg hspan η
    Real.log (euclideanCovolume ξ (hξ := hξ) L) =
      -V.degree -
        (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) *
          ((InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 -
            Real.log |(NumberField.discr K : ℝ)| / 2) := by
  let L := genericImage (K := K) M
  let hfg := genericImage_fg (K := K) M
  let hspan := genericImage_fullSpan (K := K) M
  let ξ := fullLatticeGaugeFamily L hfg hspan η
  let hξ := fullLatticeGaugeFamily_isHermitian L hfg hspan η
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct (hξ := hξ)
  let : MeasurableSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := borel _
  let : BorelSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
  have hc := originalDiagonal_covolume_eq_exp_neg_degree_sub_chi M η
  erw [originalDiagonalMap_range] at hc
  change euclideanCovolume ξ (hξ := hξ) L = _ at hc
  dsimp only
  rw [hc, Real.log_exp]

/-- Literal trace-bidual evaluation identifies the actual original arithmetic
effective-section sets, using the proved infinite-place metric equality. -/
def traceBidualEffectiveSectionsEquiv
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
    let δ := originalPrescribedTraceDualFamily M (η := η) (hη := hη)
    let hδ : δ.IsHermitian :=
      originalPrescribedTraceDualFamily_isHermitian M (η := η) (hη := hη)
    effectiveSections (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) T)
      (originalPrescribedTraceDualFamily T (hη := hδ)) ≃ effectiveSections M η := by
  let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
  let TT := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) T
  let δ := originalPrescribedTraceDualFamily M (η := η) (hη := hη)
  let hδ := originalPrescribedTraceDualFamily_isHermitian M (η := η) (hη := hη)
  let ε := originalPrescribedTraceDualFamily T (hη := hδ)
  apply Equiv.subtypeEquiv (traceBidualEquiv (K := K) M).toEquiv
  intro t
  change t ∈ effectiveSections TT ε ↔ traceBidualEquiv (K := K) M t ∈ effectiveSections M η
  erw [effectiveSections_eq_diagonal_preimage TT ε, effectiveSections_eq_diagonal_preimage M η]
  change (∀ w : InfinitePlace K, ε.norm (normalizedInfinitePlacePoint w)
      ((1 : CompletedCoefficient w) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] t)) ≤ 1) ↔
    ∀ w : InfinitePlace K, η.norm (normalizedInfinitePlacePoint w)
      ((1 : CompletedCoefficient w) ⊗ₜ[K]
        ((1 : K) ⊗ₜ[𝓞 K] traceBidualEquiv (K := K) M t)) ≤ 1
  exact forall_congr' fun w ↦ by rw [traceBidual_norm_original M w t]

/-- The actual original trace-bidual section count is the original h0. -/
theorem traceBidual_logSectionCount_eq
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
    let hδ := originalPrescribedTraceDualFamily_isHermitian M (η := η) (hη := hη)
    logSectionCount (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) T)
      (originalPrescribedTraceDualFamily T (hη := hδ)) = logSectionCount M η := by
  exact congrArg (fun n : ℕ => Real.log (n : ℝ))
    (Nat.card_congr (traceBidualEffectiveSectionsEquiv M η))

/-- The corrected two-sided Gillet–Soulé comparison on the actual original
arithmetic module, actual prescribed trace dual and actual determinant degree. -/
theorem abs_logSectionCount_sub_traceDual_sub_degree_le
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    let L := genericImage (K := K) M
    let hfg := genericImage_fg (K := K) M
    let hspan := genericImage_fullSpan (K := K) M
    let ξ := fullLatticeGaugeFamily L hfg hspan η
    let hξ : ξ.IsHermitian :=
      fullLatticeGaugeFamily_isHermitian L hfg hspan η
    let V := fullLatticeAdelicBundle L hfg hspan η
    |logSectionCount M η -
        logSectionCount (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)
          (originalPrescribedTraceDualFamily M (hη := hξ)) -
        V.degree -
        (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) *
          ((InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 -
            Real.log |(NumberField.discr K : ℝ)| / 2)| ≤
      correctedDualityConstant K (Module.finrank K (K ⊗[𝓞 K] M)) := by
  let n := Module.finrank K (K ⊗[𝓞 K] M)
  let L := genericImage (K := K) M
  let hfg := genericImage_fg (K := K) M
  let hspan := genericImage_fullSpan (K := K) M
  let ξ := fullLatticeGaugeFamily L hfg hspan η
  let hξ := fullLatticeGaugeFamily_isHermitian L hfg hspan η
  let V := fullLatticeAdelicBundle L hfg hspan η
  let D := V.degree
  let χ := (InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 -
    Real.log |(NumberField.discr K : ℝ)| / 2
  let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
  let δ := originalPrescribedTraceDualFamily M (hη := hξ)
  let hδ := originalPrescribedTraceDualFamily_isHermitian M (hη := hξ)
  let TT := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) T
  let ε := originalPrescribedTraceDualFamily T (hη := hδ)
  have hupper := logSectionCount_sub_traceDual_sub_degree_le M η
  have hlower := logTraceDual_sub_logTraceBidual_sub_logCovolume_le M ξ (hη := hξ)
  have hsections : logSectionCount M ξ = logSectionCount M η := by
    unfold logSectionCount
    rw [effectiveSections_fullLatticeGaugeFamily M η]
  change logSectionCount T δ - logSectionCount TT ε -
    Real.log (euclideanCovolume ξ (hξ := hξ) L) ≤ correctedDualityConstant K n at hlower
  rw [traceBidual_logSectionCount_eq M ξ (hη := hξ), hsections,
    log_euclideanCovolume_fullLatticeGaugeFamily M η] at hlower
  change logSectionCount M η - logSectionCount T δ - D - (n : ℝ) * χ ≤
    correctedDualityConstant K n at hupper
  change logSectionCount T δ - logSectionCount M η - (-D - (n : ℝ) * χ) ≤
    correctedDualityConstant K n at hlower
  change |logSectionCount M η - logSectionCount T δ - D - (n : ℝ) * χ| ≤ _
  exact abs_le.mpr ⟨by linarith, hupper⟩

end ArakelovGeometry.NumberFieldClassicalArithmeticDuality

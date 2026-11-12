/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Archimedean.Covolume
public import ArakelovGeometry.NumberTheory.NumberField.Archimedean.WeightedEuclidean

import ArakelovGeometry.NumberTheory.NumberField.Archimedean.WeightedJacobian
import Mathlib.Topology.Sheaves.Init

/-!
# Canonical weighted volume on the original completed product

Both measures are the canonical measures of their actual inner products.
The weighting equivalence compares two norms on the same original vectors,
with their prescribed real scalar action and literal diagonal lattice.
-/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldArchimedeanWeightedCovolume

open NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldArchimedeanWeightedEuclidean NumberFieldArchimedeanWeightedJacobian
  NumberFieldArchimedeanCovolume AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Canonical volume of the original unweighted Hermitian inner product. -/
def euclideanVolume (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian] :
    letI := euclideanNormedAddCommGroup ξ
    letI : MeasurableSpace (CompletedVectorProduct K E) := borel _
    Measure (CompletedVectorProduct K E) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct (ξ := ξ)
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  exact volume

/-- Canonical volume of the actual degree-weighted Hermitian inner product. -/
def weightedVolume (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian] :
    letI := weightedNormedAddCommGroup ξ
    letI : MeasurableSpace (CompletedVectorProduct K E) := borel _
    Measure (CompletedVectorProduct K E) := by
  let := weightedNormedAddCommGroup ξ
  let := weightedNormedSpace ξ
  let := weightedInnerProduct (ξ := ξ)
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  exact volume

/-- The original weighting map is an isometry from the weighted to the unweighted norm. -/
def weightIsometry (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    @LinearIsometryEquiv ℝ ℝ _ _ (RingHom.id ℝ) (RingHom.id ℝ) _ _
      (CompletedVectorProduct K E) (CompletedVectorProduct K E)
      (weightedNormedAddCommGroup ξ).toSeminormedAddCommGroup
      (euclideanNormedAddCommGroup ξ).toSeminormedAddCommGroup _ _ :=
  @LinearIsometryEquiv.mk ℝ ℝ _ _ (RingHom.id ℝ) (RingHom.id ℝ) _ _
    (CompletedVectorProduct K E) (CompletedVectorProduct K E)
    (weightedNormedAddCommGroup ξ).toSeminormedAddCommGroup
    (euclideanNormedAddCommGroup ξ).toSeminormedAddCommGroup _ _
    (weightEquiv (K := K) (E := E)) (fun _ => rfl)

theorem weightedVolume_eq_image
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (B : Set (CompletedVectorProduct K E)) :
    weightedVolume ξ B =
      euclideanVolume ξ (weightEquiv (K := K) (E := E) '' B) := by
  let n := euclideanNormedAddCommGroup ξ
  let nw := weightedNormedAddCommGroup ξ
  let i := euclideanInnerProduct (ξ := ξ)
  let iw := weightedInnerProduct (ξ := ξ)
  let m : MeasurableSpace (CompletedVectorProduct K E) := by
    letI := n
    exact borel _
  let mw : MeasurableSpace (CompletedVectorProduct K E) := by
    letI := nw
    exact borel _
  have b : letI := n; letI := m; BorelSpace (CompletedVectorProduct K E) := by
    let := n
    let := m
    exact ⟨rfl⟩
  have bw : letI := nw; letI := mw; BorelSpace (CompletedVectorProduct K E) := by
    let := nw
    let := mw
    exact ⟨rfl⟩
  let f := weightIsometry ξ
  let e := @LinearIsometryEquiv.toMeasurableEquiv _ _ n i nw iw mw bw m b f
  have h := @LinearIsometryEquiv.measurePreserving _ _ n i nw iw mw bw m b _ _ f
  have he := @MeasurableEquiv.map_apply _ _ mw m (weightedVolume ξ) e
    (weightEquiv (K := K) (E := E) '' B)
  change (@Measure.map _ _ mw m f (weightedVolume ξ))
    (weightEquiv (K := K) (E := E) '' B) =
      weightedVolume ξ (f ⁻¹' (weightEquiv (K := K) (E := E) '' B)) at he
  rw [@MeasurePreserving.map_eq _ _ mw m f (weightedVolume ξ)
    (euclideanVolume ξ) h] at he
  change euclideanVolume ξ (weightEquiv (K := K) (E := E) '' B) =
    weightedVolume ξ (weightEquiv (K := K) (E := E) ⁻¹'
      (weightEquiv (K := K) (E := E) '' B)) at he
  rw [Set.preimage_image_eq _ (weightEquiv (K := K) (E := E)).injective] at he
  exact he.symm

open scoped Classical in
theorem weightedVolume_eq_mul
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (B : Set (CompletedVectorProduct K E)) :
    weightedVolume ξ B =
      ENNReal.ofReal ((2 : ℝ) ^
        (Fintype.card {w : InfinitePlace K // w.IsComplex} * Module.finrank K E)) *
        euclideanVolume ξ B := by
  rw [weightedVolume_eq_image]
  exact volume_weightEquiv_image ξ B

/-- Covolume for the canonical weighted inner product of the original product. -/
def weightedCovolume (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M : Submodule (𝓞 K) E) : ℝ := by
  letI := weightedNormedAddCommGroup ξ
  letI := weightedNormedSpace ξ
  letI := weightedInnerProduct (ξ := ξ)
  letI : MeasurableSpace (CompletedVectorProduct K E) := borel _
  letI : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  letI := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  exact ZLattice.covolume (diagonalLattice M)

/-- One algebraic fundamental parallelepiped for the same original diagonal lattice. -/
def diagonalFundamentalDomain (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) : Set (CompletedVectorProduct K E) :=
  {z | ∀ i, (diagonalLatticeBasis M hfg hspan).repr z i ∈ Set.Ico 0 1}

theorem weightedCovolume_eq_fundamentalDomain
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    weightedCovolume ξ M =
      (weightedVolume ξ (diagonalFundamentalDomain M hfg hspan)).toReal := by
  let := weightedNormedAddCommGroup ξ
  let := weightedNormedSpace ξ
  let := weightedInnerProduct (ξ := ξ)
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  let := weighted_discrete_diagonalLattice ξ M hfg hspan
  let := weighted_isZLattice_diagonalLattice ξ M hfg hspan
  have hd : IsAddFundamentalDomain (diagonalLattice M)
      (ZSpan.fundamentalDomain (diagonalLatticeBasis M hfg hspan)) volume := by
    rw [diagonalLattice_eq_integerSpan M hfg hspan]
    exact ZSpan.isAddFundamentalDomain _ volume
  exact ZLattice.covolume_eq_measure_fundamentalDomain (diagonalLattice M) volume hd

theorem euclideanCovolume_eq_fundamentalDomain
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    euclideanCovolume ξ M =
      (euclideanVolume ξ (diagonalFundamentalDomain M hfg hspan)).toReal := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct (ξ := ξ)
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  let := euclidean_discrete_diagonalLattice ξ M hfg hspan
  let := euclidean_isZLattice_diagonalLattice ξ M hfg hspan
  have hd : IsAddFundamentalDomain (diagonalLattice M)
      (ZSpan.fundamentalDomain (diagonalLatticeBasis M hfg hspan)) volume := by
    rw [diagonalLattice_eq_integerSpan M hfg hspan]
    exact ZSpan.isAddFundamentalDomain _ volume
  exact ZLattice.covolume_eq_measure_fundamentalDomain (diagonalLattice M) volume hd

open scoped Classical in
theorem weightedCovolume_eq_mul
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    weightedCovolume ξ M =
      (2 : ℝ) ^ (Fintype.card {w : InfinitePlace K // w.IsComplex} * Module.finrank K E) *
        euclideanCovolume ξ M := by
  rw [weightedCovolume_eq_fundamentalDomain ξ M hfg hspan,
    euclideanCovolume_eq_fundamentalDomain ξ M hfg hspan,
    weightedVolume_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem weightedCovolume_pos
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    0 < weightedCovolume ξ M := by
  rw [weightedCovolume_eq_mul ξ M hfg hspan]
  exact mul_pos (by positivity) (euclideanCovolume_pos ξ M hfg hspan)

theorem weightedCovolume_div_eq_relIndex
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [hξ : ξ.IsHermitian]
    (M₀ M : Submodule (𝓞 K) E) (hfg₀ : M₀.FG)
    (hspan₀ : Submodule.span K (M₀ : Set E) = ⊤) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (h : M₀ ≤ M) :
    weightedCovolume ξ M₀ / weightedCovolume ξ M =
      (M₀.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
  rw [weightedCovolume_eq_mul ξ M₀ hfg₀ hspan₀,
    weightedCovolume_eq_mul ξ M hfg hspan, mul_div_mul_left _ _ (by positivity)]
  exact euclideanCovolume_div_eq_relIndex ξ M₀ M hfg₀ hspan₀ hfg hspan h

end ArakelovGeometry.NumberFieldArchimedeanWeightedCovolume

namespace ArakelovGeometry.NormFamily

open AdelicStructure NumberFieldArchimedeanWeightedCovolume NumberFieldArchimedeanCovolume

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}

open scoped Classical in
theorem IsDominated.pure_globalBall_weightedCovolume_eq
    (hdom : ξ.IsDominated) (hultra : ξ.IsUltrametric)
    (hpure : ξ.IsPureAtFinitePlaces)
    (hHerm : ξ.IsHermitian) :
    weightedCovolume ξ (ξ.globalUnitBallModule) =
      (2 : ℝ) ^ (Fintype.card {w : InfinitePlace K // w.IsComplex} * Module.finrank K E) *
        euclideanCovolume ξ (ξ.globalUnitBallModule) :=
  weightedCovolume_eq_mul ξ _
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hultra hpure).1
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hultra hpure).2.2

theorem IsDominated.pure_globalBall_weightedCovolume_pos
    (hdom : ξ.IsDominated) (hultra : ξ.IsUltrametric)
    (hpure : ξ.IsPureAtFinitePlaces)
    (hHerm : ξ.IsHermitian) :
    0 < weightedCovolume ξ (ξ.globalUnitBallModule) :=
  weightedCovolume_pos ξ _
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hultra hpure).1
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hultra hpure).2.2

end ArakelovGeometry.NormFamily

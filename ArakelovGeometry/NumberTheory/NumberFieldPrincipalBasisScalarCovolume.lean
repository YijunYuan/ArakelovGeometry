/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberFieldActualIntegerCovolume
public import ArakelovGeometry.NumberTheory.NumberFieldPrincipalBasisProductCovolume
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Scalar normalization of an original principal basis lattice

The original integral span is transported by its actual completed basis
coordinates. Its Euclidean normalization is the product of the scalar
integer normalization.
-/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldPrincipalBasisScalarCovolume

open NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanDiagonal
  NumberFieldArchimedeanEuclidean NumberFieldArchimedeanCovolume
  NumberFieldArchimedeanWeightedCovolume AdelicStructure NormFamily

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι K E)

/-- The integral span in the original vector space. -/
def principalModule : Submodule (𝓞 K) E := Submodule.span (𝓞 K) (Set.range b)

/-- The actual Hermitian family induced by the original basis. -/
abbrev basisFamily : NormFamily (normalizedNumberFieldAdelicStructure K) E :=
  ofBasisHermitian _ _ b

theorem basisFamily_hermitian :
    (basisFamily b).IsHermitian normalizedNumberFieldArchimedeanCompletions :=
  ofBasisHermitian_isHermitian b normalizedNumberFieldArchimedeanCompletions

omit [NumberField K] [Fintype ι] in
theorem mem_principalModule (x : E) :
    x ∈ principalModule b ↔ ∀ i, ∃ a : 𝓞 K, (a : K) = b.repr x i := by
  exact b.mem_span_iff_repr_mem (𝓞 K) x

omit [NumberField K] [Fintype ι] in
theorem principalModule_fg [Finite ι] : (principalModule b).FG := by
  exact Submodule.fg_span (Set.finite_range b)

omit [NumberField K] [Fintype ι] in
theorem principalModule_full :
    Submodule.span K (principalModule b : Set E) = ⊤ := by
  rw [principalModule, Submodule.span_span_of_tower, b.span_eq]

/-- Actual completed coordinates, grouped by the original basis index. -/
def basisScalarCoordinates : CompletedVectorProduct K E ≃ₗ[ℝ]
    (ι → CompletedScalarProduct K) :=
  (LinearEquiv.piCongrRight (fun w =>
    LinearEquiv.restrictScalars ℝ (b.baseChange (CompletedCoefficient w)).equivFun)).trans
      { toFun := fun z i w => z w i
        invFun := fun z w i => z i w
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }

theorem basisScalarCoordinates_diagonal (x : E) (i : ι) :
    basisScalarCoordinates b (vectorDiagonalMap (K := K) x) i =
      algebraMap K (CompletedScalarProduct K) (b.repr x i) := by
  ext w
  change (b.baseChange (CompletedCoefficient w)).equivFun (1 ⊗ₜ[K] x) i = _
  rw [basis_equivFun_one_tmul]
  rfl

variable (K) in
/-- Real coordinates of the actual scalar Euclidean mixed space. -/
abbrev ScalarRealIndex := Fin (Module.finrank ℝ (mixedEmbedding.euclidean.mixedSpace K))

open scoped Classical in
variable (K) in
def scalarEuclideanToReal : mixedEmbedding.euclidean.mixedSpace K ≃ₗ[ℝ]
    (ScalarRealIndex K → ℝ) :=
  (stdOrthonormalBasis ℝ (mixedEmbedding.euclidean.mixedSpace K)).repr.toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (ScalarRealIndex K → ℝ))

variable (K) in
/-- The mixed coordinates of the same actual completed scalar product. -/
def scalarRealCoordinates : CompletedScalarProduct K ≃ₗ[ℝ] (ScalarRealIndex K → ℝ) :=
  coefficientMixedAlgEquiv.toLinearEquiv.trans
    ((mixedEmbedding.euclidean.toMixed K).symm.toLinearEquiv.trans
      (scalarEuclideanToReal K))

open scoped Classical in
theorem scalarRealCoordinates_norm_sq (a : CompletedScalarProduct K) :
    (∑ j, ‖scalarRealCoordinates K a j‖ ^ 2) = ∑ w : InfinitePlace K, ‖a w‖ ^ 2 := by
  let := euclideanNormedAddCommGroup (NumberFieldActualIntegerCovolume.scalarFamily K)
  let := euclideanNormedSpace (NumberFieldActualIntegerCovolume.scalarFamily K)
  let z := (NumberFieldActualIntegerCovolume.scalarCoordinates K).symm a
  have h := NumberFieldActualIntegerCovolume.scalarEuclideanEquiv_norm_sq K z
  rw [euclidean_norm_sq] at h
  simp_rw [NumberFieldActualIntegerCovolume.scalarFamily_norm] at h
  change ‖(mixedEmbedding.euclidean.toMixed K).symm
      (coefficientMixedAlgEquiv (NumberFieldActualIntegerCovolume.scalarCoordinates K z))‖ ^ 2 =
    ∑ w : InfinitePlace K, ‖NumberFieldActualIntegerCovolume.scalarCoordinates K z w‖ ^ 2 at h
  rw [show NumberFieldActualIntegerCovolume.scalarCoordinates K z = a from
    (NumberFieldActualIntegerCovolume.scalarCoordinates K).apply_symm_apply a] at h
  rw [← (stdOrthonormalBasis ℝ (mixedEmbedding.euclidean.mixedSpace K)).repr.norm_map,
    EuclideanSpace.norm_sq_eq] at h
  exact h

/-- Basis coordinates in ordinary real blocks, with the original real action. -/
def basisRealCoordinates : CompletedVectorProduct K E ≃ₗ[ℝ]
    (ScalarRealIndex K × ι → ℝ) :=
  (basisScalarCoordinates b).trans
    ((LinearEquiv.piCongrRight (fun _ : ι => scalarRealCoordinates K)).trans
      NumberFieldPrincipalBasisProductCovolume.blockCoordinates)

theorem basisRealCoordinates_apply (z : CompletedVectorProduct K E)
    (j : ScalarRealIndex K) (i : ι) :
    basisRealCoordinates b z (j, i) =
      scalarRealCoordinates K (basisScalarCoordinates b z i) j := rfl

open scoped Classical in
theorem basisRealCoordinates_norm_sq (z : CompletedVectorProduct K E) :
    letI := euclideanNormedAddCommGroup (basisFamily b)
    (∑ p, ‖basisRealCoordinates b z p‖ ^ 2) = ‖z‖ ^ 2 := by
  classical
  let := euclideanNormedAddCommGroup (basisFamily b)
  rw [euclidean_norm_sq, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [basisRealCoordinates_apply, scalarRealCoordinates_norm_sq]
  rw [Finset.sum_comm]
  congr 1
  ext w
  rw [ofBasisHermitian_norm_of_infinite b _ (normalizedInfinitePlacePoint_mem_inf w),
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rfl

open scoped Classical in
def basisRealIsometry :
    letI := euclideanNormedAddCommGroup (basisFamily b)
    letI := euclideanNormedSpace (basisFamily b)
    CompletedVectorProduct K E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ScalarRealIndex K × ι) := by
  let := euclideanNormedAddCommGroup (basisFamily b)
  let := euclideanNormedSpace (basisFamily b)
  exact { toLinearEquiv := (basisRealCoordinates b).trans
            (WithLp.linearEquiv 2 ℝ (ScalarRealIndex K × ι → ℝ)).symm
          norm_map' := fun z => by
            have h := basisRealCoordinates_norm_sq b z
            rw [← EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (basisRealCoordinates b z))] at h
            change ‖WithLp.toLp 2 (basisRealCoordinates b z)‖ = ‖z‖
            nlinarith [_root_.norm_nonneg z,
              _root_.norm_nonneg (WithLp.toLp 2 (basisRealCoordinates b z))] }

open scoped Classical in
variable (K) in
/-- The real scalar coordinates are a continuous equivalence onto the mixed space. -/
def scalarRealMixedContinuousEquiv : (ScalarRealIndex K → ℝ) ≃L[ℝ]
    mixedEmbedding.mixedSpace K :=
  (scalarEuclideanToReal K).symm.toContinuousLinearEquiv.trans
    (mixedEmbedding.euclidean.toMixed K)

open scoped Classical in
theorem scalarRealMixedContinuousEquiv_coordinates (a : CompletedScalarProduct K) :
    scalarRealMixedContinuousEquiv K (scalarRealCoordinates K a) =
      coefficientMixedAlgEquiv a := by
  change mixedEmbedding.euclidean.toMixed K
    ((scalarEuclideanToReal K).symm ((scalarEuclideanToReal K)
      ((mixedEmbedding.euclidean.toMixed K).symm (coefficientMixedAlgEquiv a)))) = _
  rw [LinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]

open scoped Classical in
theorem scalarRealMixed_measurePreserving :
    MeasurePreserving (scalarRealMixedContinuousEquiv K) volume volume := by
  exact (mixedEmbedding.euclidean.volumePreserving_toMixed K).comp
    ((stdOrthonormalBasis ℝ
      (mixedEmbedding.euclidean.mixedSpace K)).measurePreserving_repr_symm.comp
      (PiLp.volume_preserving_toLp (ScalarRealIndex K)))

open scoped Classical in
variable (K) in
/-- The actual scalar integer lattice in orthonormal real coordinates. -/
def scalarRealLattice : Submodule ℤ (ScalarRealIndex K → ℝ) :=
  ZLattice.comap ℝ (mixedEmbedding.integerLattice K)
    (scalarRealMixedContinuousEquiv K).toLinearMap

instance scalarRealLattice_discrete : DiscreteTopology (scalarRealLattice K) := by
  classical
  exact ZLattice.comap_discreteTopology ℝ (mixedEmbedding.integerLattice K)
    (scalarRealMixedContinuousEquiv K).continuous
    (scalarRealMixedContinuousEquiv K).injective

instance scalarRealLattice_isZLattice : IsZLattice ℝ (scalarRealLattice K) := by
  classical
  dsimp [scalarRealLattice]
  infer_instance

open scoped Classical in
variable (K) in
/-- A real basis obtained from a genuine integer basis of the scalar lattice. -/
def scalarRealLatticeBasis : Module.Basis (ScalarRealIndex K) ℝ (ScalarRealIndex K → ℝ) :=
  (IsZLattice.basis (scalarRealLattice K)).ofZLatticeBasis ℝ (scalarRealLattice K)

theorem scalarRealLatticeBasis_span :
    Submodule.span ℤ (Set.range (scalarRealLatticeBasis K)) = scalarRealLattice K :=
  (IsZLattice.basis (scalarRealLattice K)).ofZLatticeBasis_span ℝ

theorem scalarRealLattice_coordinates (a : CompletedScalarProduct K) :
    scalarRealCoordinates K a ∈ scalarRealLattice K ↔
      ∃ x : 𝓞 K, algebraMap K (CompletedScalarProduct K) (x : K) = a := by
  classical
  change (∃ x : 𝓞 K, mixedEmbedding K (x : K) =
    scalarRealMixedContinuousEquiv K (scalarRealCoordinates K a)) ↔ _
  rw [scalarRealMixedContinuousEquiv_coordinates]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, coefficientMixedAlgEquiv.injective ?_⟩
    rw [coefficientMixedAlgEquiv_algebraMap]
    exact hx
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← coefficientMixedAlgEquiv_algebraMap, hx]

theorem scalarRealLattice_covolume :
    ZLattice.covolume (scalarRealLattice K) volume =
      (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)| := by
  classical
  rw [scalarRealLattice,
    ZLattice.covolume_comap _ volume volume (scalarRealMixed_measurePreserving (K := K)),
    ← NumberFieldActualIntegerCovolume.integerCovolume_eq_mixed]
  exact NumberFieldActualIntegerCovolume.integerCovolume K

open scoped Classical in
/-- The completed-basis equivalence with its actual Euclidean source topology. -/
def basisRealContinuousEquiv :
    letI := euclideanNormedAddCommGroup (basisFamily b)
    letI := euclideanNormedSpace (basisFamily b)
    CompletedVectorProduct K E ≃L[ℝ] (ScalarRealIndex K × ι → ℝ) := by
  let := euclideanNormedAddCommGroup (basisFamily b)
  let := euclideanNormedSpace (basisFamily b)
  exact (basisRealIsometry b).toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (ScalarRealIndex K × ι) ℝ)

theorem basisRealContinuousEquiv_apply (z : CompletedVectorProduct K E) :
    basisRealContinuousEquiv b z = basisRealCoordinates b z := rfl

open scoped Classical in
theorem principalLattice_comap :
    letI := euclideanNormedAddCommGroup (basisFamily b)
    letI := euclideanNormedSpace (basisFamily b)
    ZLattice.comap ℝ
      (NumberFieldPrincipalBasisProductCovolume.productLattice (ι := ι) (scalarRealLatticeBasis K))
      (basisRealContinuousEquiv b).toLinearMap = diagonalLattice (principalModule b) := by
  classical
  let := euclideanNormedAddCommGroup (basisFamily b)
  let := euclideanNormedSpace (basisFamily b)
  ext z
  change basisRealContinuousEquiv b z ∈
    NumberFieldPrincipalBasisProductCovolume.productLattice (scalarRealLatticeBasis K) ↔
      ∃ x : principalModule b, vectorDiagonalMap (K := K) (x : E) = z
  rw [basisRealContinuousEquiv_apply, NumberFieldPrincipalBasisProductCovolume.mem_productLattice]
  simp_rw [scalarRealLatticeBasis_span]
  change (∀ i, scalarRealCoordinates K (basisScalarCoordinates b z i) ∈ scalarRealLattice K) ↔ _
  simp_rw [scalarRealLattice_coordinates]
  constructor
  · intro h
    choose a ha using h
    let x := b.equivFun.symm (fun i => (a i : K))
    have hxcoord (i : ι) : b.repr x i = (a i : K) :=
      congrFun (b.equivFun.apply_symm_apply (fun i => (a i : K))) i
    refine ⟨⟨x, (mem_principalModule b x).2 (fun i => ⟨a i, ?_⟩)⟩, ?_⟩
    · exact (hxcoord i).symm
    · apply (basisScalarCoordinates b).injective
      apply funext
      intro i
      rw [basisScalarCoordinates_diagonal]
      rw [hxcoord]
      exact ha i
  · rintro ⟨x, hx⟩
    intro i
    obtain ⟨a, ha⟩ := (mem_principalModule b x).1 x.property i
    refine ⟨a, ?_⟩
    rw [← hx, basisScalarCoordinates_diagonal, ha]

variable [FiniteDimensional K E]

open scoped Classical in
theorem basisReal_measurePreserving :
    letI := euclideanNormedAddCommGroup (basisFamily b)
    letI := euclideanNormedSpace (basisFamily b)
    letI := euclideanInnerProduct (basisFamily_hermitian b)
    letI : MeasurableSpace (CompletedVectorProduct K E) := borel _
    letI : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
    MeasurePreserving (basisRealContinuousEquiv b) volume volume := by
  let := euclideanNormedAddCommGroup (basisFamily b)
  let := euclideanNormedSpace (basisFamily b)
  let := euclideanInnerProduct (basisFamily_hermitian b)
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  exact (PiLp.volume_preserving_ofLp (ScalarRealIndex K × ι)).comp
    (basisRealIsometry b).measurePreserving

theorem basisEuclideanCovolume :
    euclideanCovolume (basisFamily b) (basisFamily_hermitian b) (principalModule b) =
      ((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)|) ^
        Fintype.card ι := by
  classical
  let := euclideanNormedAddCommGroup (basisFamily b)
  let := euclideanNormedSpace (basisFamily b)
  let := euclideanInnerProduct (basisFamily_hermitian b)
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  let : DiscreteTopology
      (NumberFieldPrincipalBasisProductCovolume.productLattice (ι := ι)
        (scalarRealLatticeBasis K)) := by
    change DiscreteTopology (Submodule.span ℤ (Set.range
      (NumberFieldPrincipalBasisProductCovolume.blockBasis (ι := ι) (scalarRealLatticeBasis K))))
    infer_instance
  let : IsZLattice ℝ
      (NumberFieldPrincipalBasisProductCovolume.productLattice (ι := ι)
        (scalarRealLatticeBasis K)) := by
    change IsZLattice ℝ (Submodule.span ℤ (Set.range
      (NumberFieldPrincipalBasisProductCovolume.blockBasis (ι := ι) (scalarRealLatticeBasis K))))
    infer_instance
  have h := ZLattice.covolume_comap
    (NumberFieldPrincipalBasisProductCovolume.productLattice (ι := ι) (scalarRealLatticeBasis K))
    volume volume (basisReal_measurePreserving b)
  rw [principalLattice_comap] at h
  change euclideanCovolume (basisFamily b) (basisFamily_hermitian b) (principalModule b) = _ at h
  rw [h, NumberFieldPrincipalBasisProductCovolume.productCovolume,
    scalarRealLatticeBasis_span, scalarRealLattice_covolume]

theorem basisWeightedCovolume :
    weightedCovolume (basisFamily b) (basisFamily_hermitian b) (principalModule b) =
      Real.sqrt |(NumberField.discr K : ℝ)| ^ Fintype.card ι := by
  classical
  rw [weightedCovolume_eq_mul _ _ _ (principalModule_fg b) (principalModule_full b),
    basisEuclideanCovolume, Module.finrank_eq_card_basis b, pow_mul, ← mul_pow,
    ← mul_assoc, ← mul_pow]
  norm_num

end ArakelovGeometry.NumberFieldPrincipalBasisScalarCovolume

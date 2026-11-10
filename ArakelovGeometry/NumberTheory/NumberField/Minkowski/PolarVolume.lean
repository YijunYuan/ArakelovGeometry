/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.Counting.WeightedEuclideanSumBall
public import ArakelovGeometry.GeometryOfNumbers.Measure.EuclideanProductMeasure
public import ArakelovGeometry.NumberTheory.NumberField.Minkowski.Polar
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import Mathlib.Topology.Sheaves.Init

/-! # Canonical ordinary volume of the actual arithmetic product-ball polar -/

@[expose] public section

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldArithmeticPolarVolume

open AdelicStructure NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldArithmeticProductBall NumberFieldArchimedeanWeightedJacobian
  NumberFieldProjectiveTraceDualMetric NumberFieldArithmeticPolar WeightedEuclideanSumBall
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

universe u
variable {K E : Type u} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Actual original completed fibres in their separate real orthonormal blocks. -/
def blockCoordinateEquiv (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    CompletedVectorProduct K E ≃ₗ[ℝ]
      (∀ w : InfinitePlace K,
        EuclideanSpace ℝ (Fin (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E)))) :=
  (realCoordinateEquiv ξ hξ).trans
    (EuclideanProductMeasure.blockCoordinates fun w : InfinitePlace K =>
      Fin (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E)))

/-- Every block retains the literal original completed fibre norm. -/
theorem blockCoordinateEquiv_norm
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (z : CompletedVectorProduct K E) (w : InfinitePlace K) :
    ‖blockCoordinateEquiv ξ hξ z w‖ = ξ.norm (normalizedInfinitePlacePoint w) (z w) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (ξ.norm_nonneg _ _)).mp
  change ‖WithLp.toLp 2 (fun i => realCoordinateEquiv ξ hξ z ⟨w, i⟩)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simpa only [Real.norm_eq_abs, sq_abs] using (fibre_norm_sq_coordinates ξ hξ w z).symm

/-- The actual completed L2 canonical volume becomes the actual product of block volumes. -/
theorem blockCoordinateEquiv_measurePreserving
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanInnerProduct hξ
    letI : MeasurableSpace (CompletedVectorProduct K E) := borel _
    letI : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
    MeasurePreserving (blockCoordinateEquiv ξ hξ) volume volume := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  exact (EuclideanProductMeasure.blockCoordinates_measurePreserving
    (fun w : InfinitePlace K => Fin (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E)))).comp
      (realCoordinateEquiv_measurePreserving ξ hξ)

/-- The actual completed sum body, before any coordinate transport. -/
def sumBall (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    Set (CompletedVectorProduct K E) :=
  {z | (∑ w : InfinitePlace K, ξ.norm (normalizedInfinitePlacePoint w) (z w)) ≤ 1}

/-- Canonical ordinary Euclidean volume of the actual completed sum body. -/
def sumBallVolume (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) : ENNReal := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  exact volume (sumBall ξ)

/-- The full factorial volume formula on the original completed fibres and canonical measure. -/
theorem sumBallVolume_eq
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    sumBallVolume ξ hξ = ENNReal.ofReal
      ((∏ w : InfinitePlace K,
        euclideanUnitBallVolume (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E)) *
          (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E)).factorial) /
        (∑ w : InfinitePlace K, Module.finrank ℝ (CompletedCoefficient w ⊗[K] E)).factorial) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  let m (w : InfinitePlace K) := Module.finrank ℝ (CompletedCoefficient w ⊗[K] E)
  have hs : sumBall ξ = blockCoordinateEquiv ξ hξ ⁻¹'
      weightedBall (E := fun w : InfinitePlace K => EuclideanSpace ℝ (Fin (m w)))
        (fun _ => 1) := by
    ext z
    change (∑ w : InfinitePlace K, ξ.norm (normalizedInfinitePlacePoint w) (z w)) ≤ 1 ↔
      (∑ w : InfinitePlace K, 1 * ‖blockCoordinateEquiv ξ hξ z w‖) ≤ 1
    simp only [one_mul, blockCoordinateEquiv_norm]
  have hm : MeasurableSet (weightedBall
      (E := fun w : InfinitePlace K => EuclideanSpace ℝ (Fin (m w))) (fun _ => 1)) := by
    unfold weightedBall weightedNorm
    exact measurableSet_le (by fun_prop) measurable_const
  change volume (sumBall ξ) = _
  rw [hs, (blockCoordinateEquiv_measurePreserving ξ hξ).measure_preimage hm.nullMeasurableSet]
  simpa only [one_pow, div_one] using
    euclidean_volume_weightedBall m (fun _ => zero_lt_one)

/-- The arithmetic numerator, in ordinary Euclidean trace-metric coordinates. -/
def arithmeticPolarNumerator (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℝ :=
  (euclideanUnitBallVolume n * n.factorial) ^ InfinitePlace.nrRealPlaces K *
    (euclideanUnitBallVolume (2 * n) * (2 * n).factorial) ^ InfinitePlace.nrComplexPlaces K

/-- Actual completed dimensions and real/complex place multiplicities give the source numerator. -/
theorem sumBallVolume_eq_arithmeticNumerator
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    sumBallVolume ξ hξ = ENNReal.ofReal
      (arithmeticPolarNumerator K (Module.finrank K E) /
        (Module.finrank K E * Module.finrank ℚ K).factorial) := by
  classical
  rw [sumBallVolume_eq]
  simp_rw [completedFibre_real_finrank]
  have hs : (∑ w : InfinitePlace K, w.mult * Module.finrank K E) =
      Module.finrank K E * Module.finrank ℚ K := by
    rw [← Finset.sum_mul, InfinitePlace.sum_mult_eq, Nat.mul_comm]
  rw [hs, InfinitePlace.prod_eq_prod_mul_prod]
  simp only [fun w : {w : InfinitePlace K // w.IsReal} => w.property.mult_eq_one,
    fun w : {w : InfinitePlace K // w.IsComplex} => w.property.mult_eq_two,
    one_mul, Finset.prod_const, Finset.card_univ]
  rfl

/-- Hermitianity of the independently prescribed actual dual tensor family. -/
theorem prescribedTraceDualFamily_isHermitian
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    (prescribedTraceDualFamily hξ).IsHermitian normalizedNumberFieldArchimedeanCompletions := by
  exact NormFamily.orthogonalTensorPair_isHermitian ξ.dual
    (NumberFieldTraceDualizingLine.dualizingLine K).toNormFamily
    normalizedNumberFieldArchimedeanCompletions hξ.dual
    (NumberFieldTraceDualizingLine.dualizingLine_isHermitian K)

/-- Canonical source Euclidean volume of the native polar preimage under actual trace duality. -/
def arithmeticPolarVolume
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) : ENNReal := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanNormedAddCommGroup (prescribedTraceDualFamily hξ)
  let := euclideanNormedSpace (prescribedTraceDualFamily hξ)
  let := euclideanInnerProduct (prescribedTraceDualFamily_isHermitian hξ)
  let : MeasurableSpace (CompletedVectorProduct K (Module.Dual K E ⊗[K] K)) := borel _
  let : BorelSpace (CompletedVectorProduct K (Module.Dual K E ⊗[K] K)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (Module.Dual K E ⊗[K] K))
  exact volume (arithmeticTraceTensorIsometry hξ ⁻¹' StrongDual.polar ℝ (productBall ξ 1))

/-- The actual native polar preimage is the actual prescribed tensor sum body. -/
theorem arithmeticPolarVolume_eq_sumBallVolume
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    arithmeticPolarVolume hξ =
      sumBallVolume (prescribedTraceDualFamily hξ) (prescribedTraceDualFamily_isHermitian hξ) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanNormedAddCommGroup (prescribedTraceDualFamily hξ)
  let := euclideanNormedSpace (prescribedTraceDualFamily hξ)
  let := euclideanInnerProduct (prescribedTraceDualFamily_isHermitian hξ)
  let : MeasurableSpace (CompletedVectorProduct K (Module.Dual K E ⊗[K] K)) := borel _
  let : BorelSpace (CompletedVectorProduct K (Module.Dual K E ⊗[K] K)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (Module.Dual K E ⊗[K] K))
  change volume (arithmeticTraceTensorIsometry hξ ⁻¹' StrongDual.polar ℝ (productBall ξ 1)) =
    volume (sumBall (prescribedTraceDualFamily hξ))
  rw [prescribedTraceDual_polar]
  rfl

/-- Full ordinary Euclidean volume of the actual arithmetic polar, including rank zero. -/
theorem arithmeticPolarVolume_eq
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    arithmeticPolarVolume hξ = ENNReal.ofReal
      (arithmeticPolarNumerator K (Module.finrank K E) /
        (Module.finrank K E * Module.finrank ℚ K).factorial) := by
  rw [arithmeticPolarVolume_eq_sumBallVolume, sumBallVolume_eq_arithmeticNumerator]
  simp

/-- The actual trace tensor isometry preserves the canonical source and real-dual volumes.
The real-dual inner product is the existing Riesz-compatible structure, kept local. -/
theorem arithmeticTraceTensorIsometry_measurePreserving
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanInnerProduct hξ
    letI := euclideanNormedAddCommGroup (prescribedTraceDualFamily hξ)
    letI := euclideanNormedSpace (prescribedTraceDualFamily hξ)
    letI := euclideanInnerProduct (prescribedTraceDualFamily_isHermitian hξ)
    letI := GeometryOfNumbers.strongDualInnerProduct (E := CompletedVectorProduct K E)
    letI : MeasurableSpace (CompletedVectorProduct K (Module.Dual K E ⊗[K] K)) := borel _
    letI : BorelSpace (CompletedVectorProduct K (Module.Dual K E ⊗[K] K)) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace
      (E := CompletedVectorProduct K (Module.Dual K E ⊗[K] K))
    letI : MeasurableSpace (StrongDual ℝ (CompletedVectorProduct K E)) := borel _
    letI : BorelSpace (StrongDual ℝ (CompletedVectorProduct K E)) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace (E := StrongDual ℝ (CompletedVectorProduct K E))
    MeasurePreserving (arithmeticTraceTensorIsometry hξ) volume volume := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let := euclideanNormedAddCommGroup (prescribedTraceDualFamily hξ)
  let := euclideanNormedSpace (prescribedTraceDualFamily hξ)
  let := euclideanInnerProduct (prescribedTraceDualFamily_isHermitian hξ)
  let := GeometryOfNumbers.strongDualInnerProduct (E := CompletedVectorProduct K E)
  let : MeasurableSpace (CompletedVectorProduct K (Module.Dual K E ⊗[K] K)) := borel _
  let : BorelSpace (CompletedVectorProduct K (Module.Dual K E ⊗[K] K)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (Module.Dual K E ⊗[K] K))
  let : MeasurableSpace (StrongDual ℝ (CompletedVectorProduct K E)) := borel _
  let : BorelSpace (StrongDual ℝ (CompletedVectorProduct K E)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := StrongDual ℝ (CompletedVectorProduct K E))
  exact (arithmeticTraceTensorIsometry hξ).measurePreserving

/-- The literal native real-dual polar has the same canonical ordinary factorial volume. -/
theorem nativeArithmeticPolar_volume_eq
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanInnerProduct hξ
    letI := GeometryOfNumbers.strongDualInnerProduct (E := CompletedVectorProduct K E)
    letI : MeasurableSpace (StrongDual ℝ (CompletedVectorProduct K E)) := borel _
    letI : BorelSpace (StrongDual ℝ (CompletedVectorProduct K E)) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace (E := StrongDual ℝ (CompletedVectorProduct K E))
    volume (StrongDual.polar ℝ (productBall ξ 1)) = ENNReal.ofReal
      (arithmeticPolarNumerator K (Module.finrank K E) /
        (Module.finrank K E * Module.finrank ℚ K).factorial) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let := euclideanNormedAddCommGroup (prescribedTraceDualFamily hξ)
  let := euclideanNormedSpace (prescribedTraceDualFamily hξ)
  let := euclideanInnerProduct (prescribedTraceDualFamily_isHermitian hξ)
  let := GeometryOfNumbers.strongDualInnerProduct (E := CompletedVectorProduct K E)
  let : MeasurableSpace (CompletedVectorProduct K (Module.Dual K E ⊗[K] K)) := borel _
  let : BorelSpace (CompletedVectorProduct K (Module.Dual K E ⊗[K] K)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (Module.Dual K E ⊗[K] K))
  let : MeasurableSpace (StrongDual ℝ (CompletedVectorProduct K E)) := borel _
  let : BorelSpace (StrongDual ℝ (CompletedVectorProduct K E)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := StrongDual ℝ (CompletedVectorProduct K E))
  have hc : IsClosed (StrongDual.polar ℝ (productBall ξ 1)) := by
    change IsClosed {f : StrongDual ℝ (CompletedVectorProduct K E) |
      ∀ x ∈ productBall ξ 1, ‖f x‖ ≤ 1}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_le (by fun_prop) continuous_const
  have hm := (arithmeticTraceTensorIsometry_measurePreserving hξ).measure_preimage
    hc.measurableSet.nullMeasurableSet
  change arithmeticPolarVolume hξ = _ at hm
  exact hm.symm.trans (arithmeticPolarVolume_eq hξ)

end ArakelovGeometry.NumberFieldArithmeticPolarVolume

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.LatticePolarCountLower
public import ArakelovGeometry.NumberTheory.NumberFieldArithmeticPolarCount
public import ArakelovGeometry.NumberTheory.NumberFieldArithmeticSectionCount

/-! # Sharp classical arithmetic section-count and degree comparison

The ordinary native polar volume and actual trace-dual sections give the
one-sided corrected Gillet–Soulé inequality used in Chen–Moriwaki 4.3.24.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.NumberFieldClassicalCountComparison

open NumberField MeasureTheory Set
open AdelicStructure NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldArithmeticProductBall NumberFieldArithmeticPolarVolume WeightedEuclideanSumBall
  NumberFieldProjectiveGeneric NumberFieldProjectiveTraceDualGeneric NumberFieldCodifferentDual
  NumberFieldFullLattice GeometryOfNumbers
open NumberFieldInvertibleGeneric (genericImage genericImage_fullSpan)
open scoped TensorProduct ENNReal

attribute [local instance] genericFiniteDimensional
attribute [local instance] normalizedNumberFieldAdelicStructure_isProper

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The ordinary arithmetic polar numerator is strictly positive in every rank. -/
theorem arithmeticPolarNumerator_pos (n : ℕ) : 0 < arithmeticPolarNumerator K n := by
  have hv (m : ℕ) : 0 < euclideanUnitBallVolume m := by
    unfold euclideanUnitBallVolume Measure.real
    exact ENNReal.toReal_pos
      (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr zero_lt_one)).ne'
      measure_ball_lt_top.ne
  unfold arithmeticPolarNumerator
  exact mul_pos (pow_pos (mul_pos (hv n) (by positivity)) _)
    (pow_pos (mul_pos (hv (2 * n)) (by positivity)) _)

/-- The actual Hermitian product body contains the Euclidean open unit ball. -/
theorem productBall_zero_mem_interior
    {E : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    letI := euclideanNormedAddCommGroup η
    (0 : CompletedVectorProduct K E) ∈ interior (productBall η 1) := by
  let := euclideanNormedAddCommGroup η
  have hsub : Metric.ball (0 : CompletedVectorProduct K E) 1 ⊆ productBall η 1 := by
    intro z hz w
    have hzN : ‖z‖ < 1 := by simpa using hz
    have hw := Finset.single_le_sum
      (fun v (_ : v ∈ (Finset.univ : Finset (InfinitePlace K))) =>
        sq_nonneg (η.norm (normalizedInfinitePlacePoint v) (z v))) (Finset.mem_univ w)
    rw [← euclidean_norm_sq η z] at hw
    have hn := norm_nonneg z
    have hwN := η.norm_nonneg (normalizedInfinitePlacePoint w) (z w)
    nlinarith
  exact mem_interior.mpr ⟨_, hsub, Metric.isOpen_ball, Metric.mem_ball_self zero_lt_one⟩

variable (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Actual integral-dual normalization converts the ordinary native polar volume into
the original diagonal covolume times the corrected factorial volume. -/
theorem nativePolar_normalizedMeasure_eq
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup η
    letI := euclideanNormedSpace η
    letI := euclideanInnerProduct hη
    letI : MeasurableSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := borel _
    letI : BorelSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace
      (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
    letI := strongDualInnerProduct (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
    letI : MeasurableSpace (StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M))) := borel _
    letI : BorelSpace (StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M))) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace
      (E := StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M)))
    (latticeNormalizedMeasure (integralDual (originalDiagonalMap (K := K) M).range)
      volume (StrongDual.polar ℝ (productBall η 1))).toReal =
      ZLattice.covolume (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
        (originalDiagonalMap (K := K) M).range volume *
        (arithmeticPolarNumerator K (Module.finrank K (K ⊗[𝓞 K] M)) /
          (Module.finrank K (K ⊗[𝓞 K] M) * Module.finrank ℚ K).factorial) := by
  let := euclideanNormedAddCommGroup η
  let := euclideanNormedSpace η
  let := euclideanInnerProduct hη
  let : MeasurableSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := borel _
  let : BorelSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
  let := strongDualInnerProduct (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
  let : MeasurableSpace (StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M))) := borel _
  let : BorelSpace (StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M))) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M)))
  let hdisc := originalDiagonalMap_range_discrete (K := K) M η
  let hlat := originalDiagonalMap_range_isZLattice (K := K) M η
  rw [latticeNormalizedMeasure, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, nativeArithmeticPolar_volume_eq hη,
    ENNReal.toReal_ofReal (div_nonneg (arithmeticPolarNumerator_pos _).le (by positivity))]
  change (ZLattice.covolume (E := StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M)))
    (integralDual (originalDiagonalMap (K := K) M).range) volume)⁻¹ * _ = _
  have hcov := @integralDual_covolume (CompletedVectorProduct K (K ⊗[𝓞 K] M))
    (euclideanNormedAddCommGroup η) (euclideanInnerProduct hη) _ _ _
    (originalDiagonalMap (K := K) M).range hdisc hlat
  erw [hcov, inv_inv]

/-- The sharp dual-body count estimate, actual native polar volume and actual original
trace-dual section injection give an unconditional arithmetic count inequality. -/
theorem nativePolar_mul_original_count_le_traceDual_count
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup η
    letI := euclideanNormedSpace η
    letI := euclideanInnerProduct hη
    letI : MeasurableSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := borel _
    letI : BorelSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace
      (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
    ZLattice.covolume (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
        (originalDiagonalMap (K := K) M).range volume *
        (arithmeticPolarNumerator K (Module.finrank K (K ⊗[𝓞 K] M)) /
          (Module.finrank K (K ⊗[𝓞 K] M) * Module.finrank ℚ K).factorial) *
        (Nat.card (effectiveSections M η) : ℝ) ≤
      6 ^ (Module.finrank ℚ K * Module.finrank K (K ⊗[𝓞 K] M)) *
        (Nat.card (effectiveSections (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)
          (originalPrescribedTraceDualFamily M hη)) : ℝ) := by
  let := euclideanNormedAddCommGroup η
  let := euclideanNormedSpace η
  let := euclideanInnerProduct hη
  let : MeasurableSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := borel _
  let : BorelSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
  let := strongDualInnerProduct (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
  let : MeasurableSpace (StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M))) := borel _
  let : BorelSpace (StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M))) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := StrongDual ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M)))
  let hdisc := originalDiagonalMap_range_discrete (K := K) M η
  let hlat := originalDiagonalMap_range_isZLattice (K := K) M η
  have hs : ∀ z ∈ productBall η 1, -z ∈ productBall η 1 := by
    intro z hz w
    simpa only [Pi.neg_apply, map_neg_eq_map] using hz w
  have h := @LatticePolarCountLower.normalizedMeasure_polar_mul_card_le_pow_mul_card_polar
    (CompletedVectorProduct K (K ⊗[𝓞 K] M))
    (euclideanNormedAddCommGroup η) (euclideanNormedSpace η) _
    (originalDiagonalMap (K := K) M).range hdisc hlat _ _ volume _ _
    (productBall_isCompact η zero_le_one)
    (convex_productBall η 1) hs (productBall_zero_mem_interior η)
  have hcount : (Nat.card {x : (originalDiagonalMap (K := K) M).range //
      x.val ∈ productBall η 1} : ℝ) =
        (Nat.card (effectiveSections M η) : ℝ) := by
    exact_mod_cast (card_effectiveSections_eq_diagonal M η).symm
  have hvol := nativePolar_normalizedMeasure_eq M η hη
  rw [hvol] at h
  erw [hcount] at h
  rw [vectorDiagonal_dimension] at h
  have hcard :=
    NumberFieldArithmeticPolarCount.card_nativePolar_le_traceDual_effectiveSections M η hη
  apply h.trans
  gcongr
  exact hcard

/-- The actual original-module section counts and actual determinant degree satisfy
the one-sided corrected arithmetic duality estimate, including rank zero. -/
theorem logSectionCount_sub_traceDual_sub_degree_le
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    let L := genericImage (K := K) M
    let hfg := genericImage_fg (K := K) M
    let hspan := genericImage_fullSpan (K := K) M
    let ξ := fullLatticeGaugeFamily L hfg hspan η
    let hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions :=
      fullLatticeGaugeFamily_isHermitian L hfg hspan η hη
    let V := fullLatticeAdelicBundle L hfg hspan η
    logSectionCount M η -
        logSectionCount (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)
          (originalPrescribedTraceDualFamily M hξ) -
        V.degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
        (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) *
          ((InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 -
            Real.log |(NumberField.discr K : ℝ)| / 2) ≤
      (Module.finrank ℚ K : ℝ) * (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * Real.log 6 -
        Real.log (arithmeticPolarNumerator K (Module.finrank K (K ⊗[𝓞 K] M)) /
          (Module.finrank K (K ⊗[𝓞 K] M) * Module.finrank ℚ K).factorial) := by
  let n := Module.finrank K (K ⊗[𝓞 K] M)
  let d := Module.finrank ℚ K
  let L := genericImage (K := K) M
  let hfg := genericImage_fg (K := K) M
  let hspan := genericImage_fullSpan (K := K) M
  let ξ := fullLatticeGaugeFamily L hfg hspan η
  let hξ := fullLatticeGaugeFamily_isHermitian L hfg hspan η hη
  let V := fullLatticeAdelicBundle L hfg hspan η
  let D := V.degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions
  let χ := (InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 -
    Real.log |(NumberField.discr K : ℝ)| / 2
  let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
  let δ := originalPrescribedTraceDualFamily M hξ
  let Q := arithmeticPolarNumerator K n / (n * d).factorial
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := borel _
  let : BorelSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
  have hcount := nativePolar_mul_original_count_le_traceDual_count M ξ hξ
  have hcov := originalDiagonal_covolume_eq_exp_neg_degree_sub_chi (K := K) M η hη
  erw [hcov] at hcount
  have hsections : effectiveSections M ξ = effectiveSections M η :=
    effectiveSections_fullLatticeGaugeFamily M η
  rw [hsections] at hcount
  change Real.exp (-D - (n : ℝ) * χ) * Q * (Nat.card (effectiveSections M η) : ℝ) ≤
    6 ^ (d * n) * (Nat.card (effectiveSections T δ) : ℝ) at hcount
  have hQ : 0 < Q := div_pos (arithmeticPolarNumerator_pos n) (by positivity)
  have hM : 0 < (Nat.card (effectiveSections M η) : ℝ) :=
    Nat.cast_pos.mpr (card_effectiveSections_pos M η)
  have hT : 0 < (Nat.card (effectiveSections T δ) : ℝ) := by
    have hp := lt_of_lt_of_le (by positivity : 0 <
      Real.exp (-D - (n : ℝ) * χ) * Q * (Nat.card (effectiveSections M η) : ℝ)) hcount
    exact pos_of_mul_pos_right hp (by positivity)
  have hlog := Real.log_le_log (by positivity : 0 <
    Real.exp (-D - (n : ℝ) * χ) * Q * (Nat.card (effectiveSections M η) : ℝ)) hcount
  rw [Real.log_mul (mul_pos (Real.exp_pos _) hQ).ne' hM.ne',
    Real.log_mul (Real.exp_ne_zero _) hQ.ne',
    Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 6) _).ne' hT.ne',
    Real.log_exp, Real.log_pow] at hlog
  change Real.log (Nat.card (effectiveSections M η) : ℝ) -
      Real.log (Nat.card (effectiveSections T δ) : ℝ) - D - (n : ℝ) * χ ≤
    (d : ℝ) * (n : ℝ) * Real.log 6 - Real.log Q
  push_cast at hlog
  linarith

end ArakelovGeometry.NumberFieldClassicalCountComparison

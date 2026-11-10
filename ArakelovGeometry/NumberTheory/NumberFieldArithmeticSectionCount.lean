/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldProjectiveSections
import ArakelovGeometry.NumberTheory.NumberFieldProjectiveSmallVector
import ArakelovGeometry.GeometryOfNumbers.LatticeCount

/-! # Actual original-module section counts, volumes and determinant degrees -/

noncomputable section
open NumberField MeasureTheory
open scoped TensorProduct ENNReal

namespace ArakelovGeometry.NumberFieldProjectiveGeneric

open AdelicStructure NumberFieldInvertibleGeneric NumberFieldFullLattice
  NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldArithmeticProductBall NumberFieldArchimedeanWeightedCovolume

variable {K : Type*} [Field K] [NumberField K]
  (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

attribute [local instance] genericFiniteDimensional
attribute [local instance] normalizedNumberFieldAdelicStructure_isProper

omit [Module.Finite (𝓞 K) M] in
/-- The original diagonal restricts to a bijection between actual original sections
and actual lattice points in the completed product unit body. -/
def effectiveSectionsDiagonalEquiv
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    effectiveSections M η ≃
      {z : (originalDiagonalMap (K := K) M).range |
        (z : CompletedVectorProduct K (K ⊗[𝓞 K] M)) ∈ productBall η 1} := by
  apply Equiv.subtypeEquiv
    (LinearEquiv.ofInjective (originalDiagonalMap (K := K) M)
      (originalDiagonalMap_injective (K := K) M)).toEquiv
  intro m
  change m ∈ effectiveSections M η ↔
    originalDiagonalMap (K := K) M m ∈ productBall η 1
  rw [effectiveSections_eq_diagonal_preimage]
  rfl

omit [Module.Finite (𝓞 K) M] in
/-- The actual original-module count equals the count used by real lattice averaging. -/
theorem card_effectiveSections_eq_diagonal
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    Nat.card (effectiveSections M η) =
      Nat.card {z : (originalDiagonalMap (K := K) M).range |
        (z : CompletedVectorProduct K (K ⊗[𝓞 K] M)) ∈ productBall η 1} :=
  Nat.card_congr (effectiveSectionsDiagonalEquiv M η)

omit [Module.Projective (𝓞 K) M] in
/-- The canonical full-lattice replacement has exactly the original infinite norms,
so it preserves the literal original effective-section set. -/
theorem effectiveSections_fullLatticeGaugeFamily
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    effectiveSections M (fullLatticeGaugeFamily (genericImage (K := K) M)
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η) =
      effectiveSections M η := by
  ext m
  change (∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf,
    (fullLatticeGaugeFamily (genericImage (K := K) M)
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η).norm ω
        (1 ⊗ₜ[K] genericInclusion (K := K) M m) ≤ 1) ↔ _
  have heq (ω) (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf) :=
    NumberFieldFullLattice.fullLatticeGaugeFamily_norm_not_finite (genericImage (K := K) M)
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η ω hω
  constructor
  · intro hm ω hω
    simpa only [heq ω hω] using hm ω hω
  · intro hm ω hω
    rw [heq ω hω]
    exact hm ω hω

/-- The actual original-module count controls ordinary product-ball volume, with the
literal original diagonal covolume and no supplied volume or counting conclusion. -/
theorem productBallVolume_le_original_section_count
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup η
    letI := euclideanNormedSpace η
    letI := euclideanInnerProduct hη
    letI : MeasurableSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := borel _
    letI : BorelSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace
      (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
    productBallVolume η hη 1 ≤
      2 ^ (Module.finrank ℚ K * Module.finrank K (K ⊗[𝓞 K] M)) *
        (Nat.card (effectiveSections M η) : ℝ≥0∞) *
          ENNReal.ofReal (ZLattice.covolume (originalDiagonalMap (K := K) M).range) := by
  let := euclideanNormedAddCommGroup η
  let := euclideanNormedSpace η
  let := euclideanInnerProduct hη
  let : MeasurableSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := borel _
  let : BorelSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
  let := originalDiagonalMap_range_discrete (K := K) M η
  let := originalDiagonalMap_range_isZLattice (K := K) M η
  let : Countable (originalDiagonalMap (K := K) M).range := inferInstance
  let : Countable (originalDiagonalMap (K := K) M).range.toAddSubgroup :=
    inferInstanceAs (Countable (originalDiagonalMap (K := K) M).range)
  let L := genericImage (K := K) M
  let hfg := genericImage_fg (K := K) M
  let hspan := genericImage_fullSpan (K := K) M
  let b := diagonalLatticeBasis L hfg hspan
  have hF : IsAddFundamentalDomain (originalDiagonalMap (K := K) M).range
      (ZSpan.fundamentalDomain b) volume := by
    rw [originalDiagonalMap_range, diagonalLattice_eq_integerSpan L hfg hspan]
    exact ZSpan.isAddFundamentalDomain b volume
  have hvol : volume (ZSpan.fundamentalDomain b) =
      ENNReal.ofReal (ZLattice.covolume (originalDiagonalMap (K := K) M).range) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume hF]
    exact (ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne).symm
  have hsymm (z) (hz : z ∈ productBall η 1) : -z ∈ productBall η 1 := by
    intro w
    simpa only [Pi.neg_apply, map_neg_eq_map] using hz w
  have hg := LatticeCount.measure_le_two_pow_card_mul_fundamentalDomain
    (originalDiagonalMap (K := K) M).range.toAddSubgroup hF
    (productBall_isClosed η 1).measurableSet
    (productBall_isCompact η (R := 1) zero_le_one).isBounded
    (convex_productBall η 1) hsymm
  change productBallVolume η hη 1 ≤
    2 ^ Module.finrank ℝ (CompletedVectorProduct K (K ⊗[𝓞 K] M)) *
      (Nat.card {z : (originalDiagonalMap (K := K) M).range |
        (z : CompletedVectorProduct K (K ⊗[𝓞 K] M)) ∈ productBall η 1} : ℝ≥0∞) *
      volume (ZSpan.fundamentalDomain b) at hg
  rw [vectorDiagonal_dimension, ← card_effectiveSections_eq_diagonal M η, hvol] at hg
  exact hg

/-- Genuine original-module averaging and the genuine original determinant-degree
formula give the actual arithmetic section-volume estimate. -/
theorem productBallVolume_le_exp_degree_section_count
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    let L := genericImage (K := K) M
    let hfg := genericImage_fg (K := K) M
    let hspan := genericImage_fullSpan (K := K) M
    let ξ := fullLatticeGaugeFamily L hfg hspan η
    let hξ := fullLatticeGaugeFamily_isHermitian L hfg hspan η hη
    let V := fullLatticeAdelicBundle L hfg hspan η
    productBallVolume ξ hξ 1 ≤
      2 ^ (Module.finrank ℚ K * Module.finrank K (K ⊗[𝓞 K] M)) *
        (Nat.card (effectiveSections M η) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-V.degree (Or.inl inferInstance)
            normalizedNumberFieldArchimedeanCompletions -
              (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) *
                ((InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 -
                  Real.log |(NumberField.discr K : ℝ)| / 2))) := by
  let L := genericImage (K := K) M
  let hfg := genericImage_fg (K := K) M
  let hspan := genericImage_fullSpan (K := K) M
  let ξ := fullLatticeGaugeFamily L hfg hspan η
  let hξ := fullLatticeGaugeFamily_isHermitian L hfg hspan η hη
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := borel _
  let : BorelSpace (CompletedVectorProduct K (K ⊗[𝓞 K] M)) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace
    (E := CompletedVectorProduct K (K ⊗[𝓞 K] M))
  have h := productBallVolume_le_original_section_count M ξ hξ
  have hc := originalDiagonal_covolume_eq_exp_neg_degree_sub_chi (K := K) M η hη
  rw [hc, effectiveSections_fullLatticeGaugeFamily] at h
  exact h

/-- The actual inscribed cube and original diagonal count yield a coarse logarithmic
section bound. The sharper arithmetic duality constant is a separate statement. -/
theorem degree_sub_discriminant_rank_error_le_logSectionCount
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (hn : 0 < Module.finrank K (K ⊗[𝓞 K] M)) :
    let V := fullLatticeAdelicBundle (genericImage (K := K) M)
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η
    V.degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
        (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) / 2 *
          Real.log |(NumberField.discr K : ℝ)| -
        (Module.finrank ℚ K : ℝ) * (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) / 2 *
          Real.log (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) ≤ logSectionCount M η := by
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
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hcard : 0 < (Nat.card (effectiveSections M η) : ℝ) :=
    Nat.cast_pos.mpr (card_effectiveSections_pos M η)
  have hcube := productBallVolume_ge_cube ξ hξ hn (R := 1) zero_le_one
  have hupper := productBallVolume_le_exp_degree_section_count M η hη
  have he := hcube.trans hupper
  change ENNReal.ofReal ((2 : ℝ) ^ (n * Fintype.card (InfinitePlace K)) *
    (1 / Real.sqrt (n : ℝ)) ^ (d * n)) ≤
      2 ^ (d * n) * (Nat.card (effectiveSections M η) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-D - (n : ℝ) * χ)) at he
  have hreal : (2 : ℝ) ^ (n * Fintype.card (InfinitePlace K)) *
      (1 / Real.sqrt (n : ℝ)) ^ (d * n) ≤
        (2 : ℝ) ^ (d * n) * (Nat.card (effectiveSections M η) : ℝ) *
          Real.exp (-D - (n : ℝ) * χ) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [ENNReal.ofReal_mul (by positivity :
      0 ≤ (2 : ℝ) ^ (d * n) * (Nat.card (effectiveSections M η) : ℝ)),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ (d * n)),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat] using he
  have hlog := Real.log_le_log (by positivity : 0 <
    (2 : ℝ) ^ (n * Fintype.card (InfinitePlace K)) *
      (1 / Real.sqrt (n : ℝ)) ^ (d * n)) hreal
  rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne'
      (pow_pos (div_pos zero_lt_one hs) _).ne',
    Real.log_mul (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _) hcard).ne'
      (Real.exp_ne_zero _),
    Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne' hcard.ne'] at hlog
  simp only [Real.log_pow, Real.log_div one_ne_zero hs.ne', Real.log_one,
    Real.log_sqrt hnR.le, Real.log_exp] at hlog
  have hcN : Fintype.card (InfinitePlace K) + InfinitePlace.nrComplexPlaces K = d := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    have := InfinitePlace.card_add_two_mul_card_eq_rank K
    dsimp only [d]
    omega
  have hcR : (Fintype.card (InfinitePlace K) : ℝ) +
      (InfinitePlace.nrComplexPlaces K : ℝ) = (d : ℝ) := by exact_mod_cast hcN
  have hc := congrArg (fun t : ℝ => (n : ℝ) * t * Real.log 2) hcR
  change D - (n : ℝ) / 2 * Real.log |(NumberField.discr K : ℝ)| -
    (d : ℝ) * (n : ℝ) / 2 * Real.log (n : ℝ) ≤
      Real.log (Nat.card (effectiveSections M η) : ℝ)
  dsimp only [χ] at hlog
  push_cast at hlog
  nlinarith [hc]

end ArakelovGeometry.NumberFieldProjectiveGeneric

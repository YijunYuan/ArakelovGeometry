/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Slopes
public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldFullLatticeGlobalBall
public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldLatticeLambda
public import ArakelovGeometry.NumberTheory.NumberFieldArithmeticMinkowski
public import ArakelovGeometry.NumberTheory.NumberFieldArithmeticProductBall
public import ArakelovGeometry.NumberTheory.NumberFieldMinkowskiRadius

/-! # Actual nonzero integral vectors with the arithmetic Minkowski degree bound -/

@[expose] public section

noncomputable section

open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldArithmeticSmallVector

open AdelicStructure NumberFieldFullLattice NumberFieldArchimedeanVectorDiagonal
  NumberFieldArchimedeanEuclidean NumberFieldArchimedeanCovolume
  NumberFieldArchimedeanWeightedCovolume
  NumberFieldArithmeticProductBall NumberFieldArithmeticMinkowski

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

attribute [local instance] normalizedNumberFieldAdelicStructure_isProper

local instance smallVectorDiscreteMeasurable :
    DiscreteMeasurableSpace (normalizedNumberFieldAdelicStructure K).Ω :=
  inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})

omit [FiniteDimensional K E] in
/-- Membership of the original diagonal vector in the actual product body is the original
infinite maximum bound, with its zero endpoint retained. -/
theorem diagonal_mem_productBall_iff
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (s : E)
    {R : ℝ} (hR : 0 ≤ R) :
    vectorDiagonalMap (K := K) (E := E) s ∈ productBall ξ R ↔
      ξ.archimedeanMaxNorm s ≤ R := by
  rw [ξ.archimedeanMaxNorm_le_iff s hR]
  constructor
  · intro hs ω hω
    obtain ⟨w, rfl⟩ := normalizedNumberFieldAdelicStructure_Ωinf_eq_range.le hω
    exact hs w
  · intro hs w
    exact hs _ (normalizedInfinitePlacePoint_mem_inf w)

/-- The actual lattice contains a nonzero original vector inside the produced arithmetic
Minkowski radius. Its volume premise is proved from the actual degree and cube estimate. -/
theorem exists_integral_nonzero_archimedean_bound
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (hn : 0 < Module.finrank K E) :
    let V := fullLatticeAdelicBundle L hfg hspan η
    ∃ s : {x : E // x ≠ 0}, s.val ∈ L ∧
      V.toNormFamily.archimedeanMaxNorm s.val ≤ NumberFieldMinkowskiRadius.radius K
        (Module.finrank K E) (V.degree (Or.inl inferInstance)
          normalizedNumberFieldArchimedeanCompletions) := by
  let V := fullLatticeAdelicBundle L hfg hspan η
  let ξ := fullLatticeGaugeFamily L hfg hspan η
  let hξ := fullLatticeGaugeFamily_isHermitian L hfg hspan η hη
  let D := V.degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions
  let R := NumberFieldMinkowskiRadius.radius K (Module.finrank K E) D
  have hR : 0 < R := NumberFieldMinkowskiRadius.radius_pos K hn D
  have hv : ENNReal.ofReal (euclideanCovolume ξ hξ L) *
      2 ^ (Module.finrank ℚ K * Module.finrank K E) ≤
        euclideanVolume ξ hξ (productBall ξ R) := by
    change _ ≤ productBallVolume ξ hξ R
    rw [fullLattice_euclideanCovolume_eq_exp_neg_degree L hfg hspan η hη]
    have he := NumberFieldMinkowskiRadius.volume_threshold_identity K hn D
    rw [show (2 : ENNReal) ^ (Module.finrank ℚ K * Module.finrank K E) =
      ENNReal.ofReal ((2 : ℝ) ^ (Module.finrank ℚ K * Module.finrank K E)) by
        simp, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← he]
    exact productBallVolume_ge_cube ξ hξ hn hR.le
  obtain ⟨s, hsL, hs0, hsB⟩ := exists_integral_nonzero_of_convex_volume ξ hξ L hfg
    hspan hn (productBall ξ R) (productBall_isCompact ξ hR.le)
      (convex_productBall ξ R) (fun z hz => by
        rw [← neg_productBall ξ R]
        simpa only [Set.mem_neg, neg_neg] using hz) hv
  refine ⟨⟨s, hs0⟩, hsL, ?_⟩
  exact (diagonal_mem_productBall_iff ξ s hR.le).mp hsB

/-- The source arithmetic large-degree vector bound on the original finite full lattice,
with the actual determinant degree and unnormalized number-field place masses. -/
theorem exists_integral_nonzero_large_degree
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (hn : 0 < Module.finrank K E) :
    let V := fullLatticeAdelicBundle L hfg hspan η
    ∃ s : {x : E // x ≠ 0}, s.val ∈ L ∧
      V.slope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions -
        (Module.finrank ℚ K : ℝ) / 2 * Real.log (Module.finrank K E : ℝ) -
          Real.log |(NumberField.discr K : ℝ)| / 2 ≤
            V.toNormFamily.vectorDegree V.isDominated V.isMeasurable s := by
  let V := fullLatticeAdelicBundle L hfg hspan η
  let D := V.degree (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions
  let R := NumberFieldMinkowskiRadius.radius K (Module.finrank K E) D
  have hR : 0 < R := NumberFieldMinkowskiRadius.radius_pos K hn D
  obtain ⟨s, hsL, hsR⟩ := exists_integral_nonzero_archimedean_bound L hfg hspan η hη hn
  have hsball : s.val ∈ V.toNormFamily.globalUnitBall := by
    change s.val ∈ (fullLatticeGaugeFamily L hfg hspan η).globalUnitBall
    rwa [fullLatticeGaugeFamily_globalUnitBall_eq]
  have hsbound : V.toNormFamily.archimedeanMaxNorm s.val ≤ Real.exp (-(-Real.log R)) := by
    simpa only [neg_neg, Real.exp_log hR] using hsR
  have hd := V.toNormFamily.vectorDegree_ge_of_integral_archimedean_bound
    V.isDominated V.isMeasurable s hsball hsbound
  refine ⟨s, hsL, ?_⟩
  have he := NumberFieldMinkowskiRadius.neg_rank_mul_log_radius K hn D
  change -(Module.finrank ℚ K : ℝ) * Real.log R = _ at he
  rw [mul_neg, ← neg_mul, he] at hd
  exact hd

end ArakelovGeometry.NumberFieldArithmeticSmallVector

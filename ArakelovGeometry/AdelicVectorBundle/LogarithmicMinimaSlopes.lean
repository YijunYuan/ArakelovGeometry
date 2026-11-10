/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.LogarithmicMinimaBasis
public import ArakelovGeometry.AdelicVectorBundle.SlopesQuotient

/-!
# Actual last logarithmic minimum and actual minimal slope

Completed quotient contraction transports high-degree rational generators.
Their actual quotient bases feed Hadamard and integrable determinant norms,
so every nonzero quotient mean dominates each full-span threshold. Taking the
actual quotient infimum and threshold supremum proves source Proposition4.3.77,
without an attainment premise. Original degree regularity remains explicit.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} {E : Type w}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Actual completed quotient contraction increases the degree of each
nonzero rational section with nonzero quotient image. -/
theorem vectorDegree_le_quotientOfMeasurableBase (V : AdelicVectorBundle S E)
    (U : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (s : {x : E // x ≠ 0}) (hq : U.mkQ s.val ≠ 0) :
    V.vectorDegree s ≤
      (V.quotientOfMeasurableBase U hS).vectorDegree ⟨U.mkQ s.val, hq⟩ := by
  let Q := V.quotientOfMeasurableBase U hS
  simp only [vectorDegree, NormFamily.vectorDegree_eq_neg_integral]
  apply neg_le_neg
  apply integral_mono (Q.integrable_logNorm _) (V.integrable_logNorm _)
  intro ω
  apply Real.log_le_log (Q.toNormFamily.norm_rational_pos ω hq)
  change (V.toNormFamily.quotient U).norm ω (1 ⊗ₜ[K] U.mkQ s.val) ≤
    V.toNormFamily.norm ω (1 ⊗ₜ[K] s.val)
  simpa only [LinearMap.baseChange_tmul] using
    V.toNormFamily.quotient_norm_mk_le U ω (1 ⊗ₜ[K] s.val)

/-- Images of actual high-degree generators belong to the genuine quotient
threshold span, including those whose quotient image is zero. -/
theorem degreeThresholdSpan_quotient_map_le (V : AdelicVectorBundle S E)
    (U : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) (t : ℝ) :
    (V.degreeThresholdSpan t).map U.mkQ ≤
      (V.quotientOfMeasurableBase U hS).degreeThresholdSpan t := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro x ⟨hx, ht⟩
  change U.mkQ x ∈ (V.quotientOfMeasurableBase U hS).degreeThresholdSpan t
  by_cases hq : U.mkQ x = 0
  · rw [hq]
    exact Submodule.zero_mem _
  · exact (V.quotientOfMeasurableBase U hS).mem_degreeThresholdSpan
      ⟨U.mkQ x, hq⟩ (ht.trans (V.vectorDegree_le_quotientOfMeasurableBase U hS ⟨x, hx⟩ hq))

/-- Integrating actual completed Hadamard bounds the sum of the actual
basis-vector degrees by the actual determinant degree, also in rank zero. -/
theorem sum_vectorDegree_basis_le_degree [S.IsProper] (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (b : Module.Basis (Fin (Module.finrank K E)) K E) :
    (∑ j, V.vectorDegree ⟨b j, b.ne_zero j⟩) ≤ V.degree hS hN := by
  classical
  let w := exteriorPower.ιMulti K (Module.finrank K E) b
  have hw : w ≠ 0 := by
    intro hz
    have he := congrArg (determinantCoordinateEquiv b) hz
    rw [determinantCoordinateEquiv_ιMulti, Module.Basis.det_self, map_zero] at he
    exact one_ne_zero he
  have hl (ω : S.Ω) : V.toNormFamily.determinant.logNorm w ω ≤
      ∑ j, V.toNormFamily.logNorm (b j) ω := by
    have h := V.toNormFamily.determinant_norm_ιMulti_le ω
      (fun j => (1 : (S.ϕ ω).Completion) ⊗ₜ[K] b j)
    rw [exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one] at h
    have hp := Real.log_le_log (V.toNormFamily.determinant.norm_rational_pos ω hw) h
    rw [Real.log_prod (fun j _ => (V.toNormFamily.norm_rational_pos ω (b.ne_zero j)).ne')] at hp
    exact hp
  have hi := integral_mono
    ((V.determinantOfMeasurableBase hS hN).integrable_logNorm w)
    (integrable_finsetSum Finset.univ (fun j _ => V.integrable_logNorm (b j))) hl
  rw [integral_finsetSum Finset.univ (fun j _ => V.integrable_logNorm (b j))] at hi
  rw [V.degree_eq_neg_integral hS hN ⟨w, hw⟩]
  simp only [vectorDegree, NormFamily.vectorDegree_eq_neg_integral, Finset.sum_neg_distrib]
  exact neg_le_neg hi

/-- A full actual ambient threshold span produces a genuine quotient basis
with every actual quotient vector degree above the same threshold. -/
theorem exists_basis_quotient_degree_ge_of_thresholdSpan_eq_top
    (V : AdelicVectorBundle S E) (U : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    {t : ℝ} (hspan : V.degreeThresholdSpan t = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank K (E ⧸ U))) K (E ⧸ U),
      ∀ j, t ≤ (V.quotientOfMeasurableBase U hS).vectorDegree ⟨b j, b.ne_zero j⟩ := by
  classical
  let Q := V.quotientOfMeasurableBase U hS
  have hmap := V.degreeThresholdSpan_quotient_map_le U hS t
  rw [hspan, Submodule.map_top, LinearMap.range_eq_top.mpr U.mkQ_surjective] at hmap
  have hQ : Q.degreeThresholdSpan t = ⊤ := top_unique hmap
  obtain ⟨s, hli, hs⟩ := (Q.le_finrank_degreeThresholdSpan_iff
    (Module.finrank K (E ⧸ U)) t).mp (by rw [hQ, finrank_top])
  let b := basisOfLinearIndependentOfCardEqFinrank' (fun j => (s j).val) hli (by simp)
  refine ⟨b, ?_⟩
  intro j
  simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using hs j

/-- The actual determinant degree of every quotient is at least its rank
times an actual full-span threshold of the original bundle. -/
theorem rank_mul_le_degree_quotient_of_thresholdSpan_eq_top [S.IsProper]
    (V : AdelicVectorBundle S E) (U : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {t : ℝ} (hspan : V.degreeThresholdSpan t = ⊤) :
    (Module.finrank K (E ⧸ U) : ℝ) * t ≤
      (V.quotientOfMeasurableBase U hS).degree hS hN := by
  classical
  obtain ⟨b, hb⟩ := V.exists_basis_quotient_degree_ge_of_thresholdSpan_eq_top U hS hspan
  calc
    (Module.finrank K (E ⧸ U) : ℝ) * t = ∑ _j : Fin (Module.finrank K (E ⧸ U)), t := by simp
    _ ≤ ∑ j, (V.quotientOfMeasurableBase U hS).vectorDegree ⟨b j, b.ne_zero j⟩ :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ ≤ (V.quotientOfMeasurableBase U hS).degree hS hN :=
      (V.quotientOfMeasurableBase U hS).sum_vectorDegree_basis_le_degree hS hN b

/-- Positive-rank actual quotient mean slopes dominate each actual full-span
threshold; the degree bound supplies the conclusion rather than a premise. -/
theorem le_slope_quotient_of_thresholdSpan_eq_top [S.IsProper]
    (V : AdelicVectorBundle S E) (U : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hU : 0 < Module.finrank K (E ⧸ U))
    {t : ℝ} (hspan : V.degreeThresholdSpan t = ⊤) :
    t ≤ (V.quotientOfMeasurableBase U hS).slope hS hN := by
  have hd := V.rank_mul_le_degree_quotient_of_thresholdSpan_eq_top U hS hN hspan
  rw [(V.quotientOfMeasurableBase U hS).degree_eq_rank_mul_slope hS hN] at hd
  exact (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hU : (0 : ℝ) < _)).mp hd

/-- Source Proposition4.3.77 for the genuine quotient-mean infimum.
The rank-zero natural-index convention also holds, with both sides `⊤`.
No finite-value or attained-basis premise at the last minimum is used. -/
theorem minimalLogarithmicMinimum_le_minimalSlope [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.minimalLogarithmicMinimum ≤ V.minimalSlope hS hN := by
  rw [minimalLogarithmicMinimum, logarithmicMinimum,
    V.minimalSlope_eq_iInf_slope_quotient hS hN]
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  have hspan : V.degreeThresholdSpan t = ⊤ :=
    Submodule.eq_top_of_finrank_eq (Nat.le_antisymm
      (Submodule.finrank_le _) ht)
  apply le_iInf
  intro U
  exact_mod_cast V.le_slope_quotient_of_thresholdSpan_eq_top U.val hS hN U.property hspan

end ArakelovGeometry.AdelicVectorBundle

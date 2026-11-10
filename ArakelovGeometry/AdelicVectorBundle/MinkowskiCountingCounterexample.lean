/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.MinkowskiCountingBundle
import ArakelovGeometry.AdelicVectorBundle.LineVectorDegree
import ArakelovGeometry.AdelicVectorBundle.Minkowski
import ArakelovGeometry.AdelicVectorBundle.StrongMinkowskiImplication
import ArakelovGeometry.AdelicVectorBundle.Destabilizing
import ArakelovGeometry.Analysis.DeterminantExactSequence

/-!
# The actual counting-curve obstruction to every finite Minkowski level

Determinant norms, degrees, and ordinary minima are calculated from the
completed finite-truncation bundles. The source cost is `exp (-1)`.

Canonical isometric copies give counterexamples in every vector-space universe.
The counting curve has zero Archimedean mass, so the same curve also has no
finite strong Minkowski level. It gives no counterexample to the unrestricted
same-level strong-to-ordinary implication of source Remark 4.3.81.
-/

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.MinkowskiCounting
noncomputable section
open AdelicStructure CountingDominationCounterexample

local instance : DecidablePred (fun x : ℚ ↦ x = 0) :=
  fun _ ↦ Classical.propDecidable _

/-- The original counting curve is discrete, so the actual degree API applies. -/
theorem countingRegularity : DiscreteMeasurableSpace countingCurve.Ω ∨
    countingCurve.HasCommonCountableDenseSubfield := Or.inl inferInstance

/-- There are no archimedean places in the original trivial counting curve. -/
theorem countingArchimedeanNormalization :
    ∀ a ∈ countingCurve.Ωinf, IsRCLikeNormedField (countingCurve.ϕ a).Completion := by
  intro a ha
  have h := AbsoluteValue.isNonarchimedeanPlace_trivialPlace (K := ℚ)
  simp only [AbsoluteValue.IsNonarchimedeanPlace, AbsoluteValue.trivialPlace_out_eq] at h
  exact (ha h).elim

/-- The actual plane has rank two. -/
theorem finrank_plane : Module.finrank ℚ Plane = 2 := by
  simp [Plane, Module.finrank_prod]

/-- The actual rational plane basis with its literal finrank index. -/
def rankBasis : Module.Basis (Fin (Module.finrank ℚ Plane)) ℚ Plane :=
  (Module.Basis.finTwoProd ℚ).reindex (finCongr finrank_plane.symm)

/-- The genuine nonzero top-wedge generator of the rational plane. -/
def determinantVector : ⋀[ℚ]^(Module.finrank ℚ Plane) Plane :=
  exteriorPower.ιMulti ℚ _ rankBasis

/-- Nonvanishing is proved by the canonical determinant coordinate. -/
theorem determinantVector_ne_zero : determinantVector ≠ 0 := by
  intro hz
  have h := congrArg (determinantCoordinateEquiv rankBasis) hz
  simp only [determinantVector, determinantCoordinateEquiv_ιMulti,
    Module.Basis.det_self, map_zero] at h
  exact one_ne_zero h

private theorem finTwoProd_det (v : Fin 2 → Plane) :
    (Module.Basis.finTwoProd ℚ).det v = (v 0).1 * (v 1).2 - (v 0).2 * (v 1).1 := by
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, Module.Basis.coe_finTwoProd_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

private theorem cost_le_product_of_det_ne_zero (c : ℝ) (hc1 : c ≤ 1)
    (a : ℚ) (v : Fin 2 → Plane) (hv : (Module.Basis.finTwoProd ℚ).det v ≠ 0) :
    c ≤ ∏ i, rawNorm c a (v i) := by
  classical
  have hx : v 0 ≠ 0 := by
    intro h
    apply hv
    rw [finTwoProd_det, h]
    simp
  have hy : v 1 ≠ 0 := by
    intro h
    apply hv
    rw [finTwoProd_det, h]
    simp
  rw [Fin.prod_univ_two]
  by_cases h0 : (v 0).2 = a * (v 0).1
  · have h1 : (v 1).2 ≠ a * (v 1).1 := by
      intro h1
      apply hv
      rw [finTwoProd_det, h0, h1]
      ring
    have hn : rawNorm c a (v 1) = 1 := by
      rw [rawNorm, if_neg hy, if_neg h1]
    rw [hn, mul_one]
    exact cost_le_rawNorm hc1 a hx
  · have hn : rawNorm c a (v 0) = 1 := by
      rw [rawNorm, if_neg hx, if_neg h0]
    rw [hn, one_mul]
    exact cost_le_rawNorm hc1 a hy

private theorem rankBasis_det_cheap (a : ℚ) :
    rankBasis.det ((cheapBasis a).reindex (finCongr finrank_plane.symm)) = 1 := by
  classical
  rw [rankBasis, Module.Basis.det_reindex]
  have he : ((cheapBasis a).reindex (finCongr finrank_plane.symm)) ∘
      (finCongr finrank_plane.symm) = cheapBasis a := by
    funext i
    simp only [Function.comp_apply, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  rw [he, finTwoProd_det, cheapBasis_zero, cheapBasis_one]
  norm_num

private theorem cheap_wedge_eq_determinantVector (a : ℚ) :
    exteriorPower.ιMulti ℚ (Module.finrank ℚ Plane)
      ((cheapBasis a).reindex (finCongr finrank_plane.symm)) = determinantVector := by
  apply (determinantCoordinateEquiv rankBasis).injective
  rw [determinantCoordinateEquiv_ιMulti, rankBasis_det_cheap, determinantVector,
    determinantCoordinateEquiv_ιMulti, Module.Basis.det_self]

private theorem determinant_norm_generator_of_rawNorm (ξ : NormFamily countingCurve Plane)
    (a : countingCurve.Ω) (c : ℝ) (hc1 : c ≤ 1)
    (hξ : ∀ x : Plane, ξ.norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] x) =
      rawNorm c a x) :
    ξ.determinant.norm a ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] determinantVector) =
      c := by
  classical
  let e : Fin 2 ≃ Fin (Module.finrank ℚ Plane) := finCongr finrank_plane.symm
  let b := (cheapBasis a).reindex e
  let v := fun i ↦ (1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] b i
  have hw : (exteriorBaseChangeEquiv ℚ (countingCurve.ϕ a).Completion Plane _).symm
      (exteriorPower.ιMulti (countingCurve.ϕ a).Completion _ v) =
        (1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] determinantVector := by
    rw [exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one]
    exact congrArg (fun z ↦ (1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] z)
      (cheap_wedge_eq_determinantVector a)
  have hp : (∏ i, ξ.norm a (v i)) = c := by
    rw [← e.prod_comp (fun i ↦ ξ.norm a (v i))]
    simp only [v, b, Module.Basis.reindex_apply, Equiv.symm_apply_apply, hξ,
      Fin.prod_univ_two, cheapBasis_zero, cheapBasis_one]
    simp [rawNorm]
  apply le_antisymm
  · rw [← hw]
    exact (ξ.determinant_norm_ιMulti_le a v).trans_eq hp
  rw [ξ.determinant_norm_eq_sInf_ιMulti (by rw [finrank_plane]; norm_num)]
  refine le_csInf ⟨c, v, hw, hp⟩ ?_
  rintro _ ⟨u, hu, rfl⟩
  let w : Fin (Module.finrank ℚ Plane) → Plane :=
    fun i ↦ trivialCompletedTensorEquiv ℚ Plane (u i)
  have he : u = fun i ↦ (1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] w i := by
    funext i
    exact completed_eq_one_tmul a (u i)
  have hw' : exteriorPower.ιMulti ℚ (Module.finrank ℚ Plane) w = determinantVector := by
    apply NormFamily.rational_tmul_injective (S := countingCurve) a
    rw [he, exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one] at hu
    exact hu
  have hd : rankBasis.det w ≠ 0 := by
    have hh := congrArg (determinantCoordinateEquiv rankBasis) hw'
    rw [determinantCoordinateEquiv_ιMulti, determinantVector,
      determinantCoordinateEquiv_ιMulti, Module.Basis.det_self] at hh
    rw [hh]
    exact one_ne_zero
  rw [he, ← e.prod_comp (fun i ↦ ξ.norm a
    ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] w i))]
  simp only [hξ]
  apply cost_le_product_of_det_ne_zero c hc1 a (w ∘ e)
  simpa only [rankBasis, Module.Basis.det_reindex] using hd

private theorem truncatedFamily_rational_rawNorm (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (a : countingCurve.Ω) (x : Plane) :
    (truncatedFamily s c hc hc1).norm a
      ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] x) =
        rawNorm (if a ∈ s then c else 1) a x := by
  classical
  rw [truncatedFamily_norm_rational]
  by_cases ha : a ∈ s
  · simp [rawNorm, ha]
  · simp only [ha, false_and, if_false, rawNorm]
    split_ifs <;> rfl

/-- Exact determinant normalization on the genuine rational top-wedge generator. -/
theorem truncatedFamily_determinant_norm_generator (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (a : countingCurve.Ω) :
    (truncatedFamily s c hc hc1).determinant.norm a
      ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] determinantVector) =
        if a ∈ s then c else 1 := by
  classical
  apply determinant_norm_generator_of_rawNorm
  · split_ifs
    · exact hc1
    · exact le_rfl
  · exact truncatedFamily_rational_rawNorm s c hc hc1 a

/-- Every nonzero rational determinant has the same exact local cost. -/
theorem truncatedFamily_determinant_norm_rational (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (a : countingCurve.Ω)
    (d : ⋀[ℚ]^(Module.finrank ℚ Plane) Plane) (hd : d ≠ 0) :
    (truncatedFamily s c hc hc1).determinant.norm a
      ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] d) =
        if a ∈ s then c else 1 := by
  classical
  let r := determinantCoordinateEquiv rankBasis d
  have hr : r ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hd
  have he : d = r • determinantVector := by
    apply (determinantCoordinateEquiv rankBasis).injective
    simp only [map_smul, determinantVector, determinantCoordinateEquiv_ιMulti,
      Module.Basis.det_self, smul_eq_mul, mul_one]
    rfl
  have ht : (1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] (r • determinantVector) =
      (algebraMap ℚ (countingCurve.ϕ a).Completion r) •
        ((1 : (countingCurve.ϕ a).Completion) ⊗ₜ[ℚ] determinantVector) := by
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [he, ht, (truncatedFamily s c hc hc1).determinant.norm_smul,
    norm_trivialCompletion ℚ, trivialCompletionAlgEquiv_algebraMap]
  rw [AbsoluteValue.trivial_apply hr, one_mul,
    truncatedFamily_determinant_norm_generator]

private theorem integral_finite_profile (s : Finset ℚ) (r : ℝ) :
    ∫ a : countingCurve.Ω, (if a ∈ s then r else 0) ∂countingCurve.v =
      (s.card : ℝ) * r := by
  classical
  have hf : Integrable (fun a : countingCurve.Ω ↦ if a ∈ s then r else 0)
      countingCurve.v := by
    apply integrable_count_iff.mpr
    apply summable_of_ne_finset_zero (s := s)
    intro a ha
    simp [ha]
  rw [integral_countable hf]
  have hm (a : countingCurve.Ω) : countingCurve.v.real {a} = 1 := by
    simp [measureReal_def]
  simp only [hm, one_smul]
  rw [tsum_eq_sum (s := s) (fun a ha ↦ by simp [ha])]
  simp

/-- The degree is the actual determinant log integral over all original counting places. -/
theorem bundle_degree (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (bundle s c hc hc1).degree countingRegularity countingArchimedeanNormalization =
      (s.card : ℝ) * (-Real.log c) := by
  rw [(bundle s c hc hc1).degree_eq_neg_integral countingRegularity
    countingArchimedeanNormalization ⟨determinantVector, determinantVector_ne_zero⟩]
  have he : (bundle s c hc hc1).toNormFamily.determinant.logNorm determinantVector =
      fun a ↦ if a ∈ s then Real.log c else 0 := by
    funext a
    change Real.log ((truncatedFamily s c hc hc1).determinant.norm a _) = _
    rw [truncatedFamily_determinant_norm_generator]
    split_ifs <;> simp
  rw [he, integral_finite_profile]
  ring

/-- The exact vector degree counts only selected places on its actual rational line. -/
theorem bundle_vectorDegree (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (x : {x : Plane // x ≠ 0}) :
    (bundle s c hc hc1).vectorDegree x =
      ((s.filter fun a ↦ x.val.2 = a * x.val.1).card : ℝ) * (-Real.log c) := by
  classical
  rw [AdelicVectorBundle.vectorDegree, NormFamily.vectorDegree_eq_neg_integral]
  have he : (bundle s c hc hc1).toNormFamily.logNorm x.val =
      fun a ↦ if a ∈ s.filter (fun a ↦ x.val.2 = a * x.val.1)
        then Real.log c else 0 := by
    funext a
    rw [bundle_toNormFamily, truncatedFamily_logNorm s c hc hc1 a x.property]
    simp only [Finset.mem_filter]
  rw [he, integral_finite_profile]
  ring

private theorem cheap_places_card_le_one (s : Finset ℚ) (x : {x : Plane // x ≠ 0}) :
    (s.filter fun a ↦ x.val.2 = a * x.val.1).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  have hx : x.val.1 ≠ 0 := by
    intro hz
    have hy : x.val.2 = 0 := by simpa only [hz, mul_zero] using ha.2
    exact x.property (Prod.ext hz hy)
  exact (mul_right_cancel₀ hx) (ha.2.symm.trans hb.2)

/-- Every actual vector degree is bounded independently of the number of selected places. -/
theorem bundle_vectorDegree_le (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (x : {x : Plane // x ≠ 0}) :
    (bundle s c hc hc1).vectorDegree x ≤ -Real.log c := by
  rw [bundle_vectorDegree]
  have hcard : ((s.filter fun a ↦ x.val.2 = a * x.val.1).card : ℝ) ≤ 1 :=
    by exact_mod_cast cheap_places_card_le_one s x
  exact (mul_le_mul_of_nonneg_right hcard
    (neg_nonneg.mpr (Real.log_nonpos hc.le hc1))).trans_eq (one_mul _)

/-- Every selected cheap line attains the vector-degree bound on a nonzero actual section. -/
theorem bundle_vectorDegree_cheap (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (a : ℚ) (ha : a ∈ s) :
    (bundle s c hc hc1).vectorDegree ⟨(1,a), by simp⟩ = -Real.log c := by
  classical
  rw [bundle_vectorDegree]
  have he : s.filter (fun b ↦ ((1,a) : Plane).2 = b * ((1,a) : Plane).1) = {a} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_singleton, mul_one]
    constructor
    · rintro ⟨_, hab⟩
      exact hab.symm
    · rintro rfl
      exact ⟨ha, rfl⟩
  rw [he]
  simp

private theorem maximalLogarithmicMinimum_le_of_vectorDegree_le
    (V : AdelicVectorBundle countingCurve Plane) (r : ℝ)
    (hV : ∀ x, V.vectorDegree x ≤ r) :
    V.maximalLogarithmicMinimum ≤ (r : EReal) := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨x, _, hx⟩ := (V.le_finrank_degreeThresholdSpan_iff 1 t).mp ht
  exact EReal.coe_le_coe_iff.mpr ((hx 0).trans (hV (x 0)))

private theorem vectorDegree_le_maximalLogarithmicMinimum
    (V : AdelicVectorBundle countingCurve Plane) (x : {x : Plane // x ≠ 0}) :
    (V.vectorDegree x : EReal) ≤ V.maximalLogarithmicMinimum := by
  exact V.coe_le_logarithmicMinimum_of_linearIndependent (fun _ : Fin 1 ↦ x)
    (linearIndependent_unique_iff.mpr x.property) (fun _ ↦ le_rfl)

/-- The actual first minimum is attained at a selected cheap section. -/
theorem bundle_maximalLogarithmicMinimum (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hs : s.Nonempty) :
    (bundle s c hc hc1).maximalLogarithmicMinimum = (-Real.log c : EReal) := by
  apply le_antisymm
  · exact maximalLogarithmicMinimum_le_of_vectorDegree_le _ _
      (bundle_vectorDegree_le s c hc hc1)
  obtain ⟨a, ha⟩ := hs
  have h := vectorDegree_le_maximalLogarithmicMinimum (bundle s c hc hc1)
    ⟨(1,a), by simp⟩
  rw [bundle_vectorDegree_cheap s c hc hc1 a ha] at h
  exact h

/-- The empty selected set gives first minimum zero on the actual rank-two plane. -/
theorem bundle_maximalLogarithmicMinimum_empty (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (bundle ∅ c hc hc1).maximalLogarithmicMinimum = (0 : EReal) := by
  have hv (x : {x : Plane // x ≠ 0}) : (bundle ∅ c hc hc1).vectorDegree x = 0 := by
    rw [bundle_vectorDegree]
    simp
  apply le_antisymm
  · exact maximalLogarithmicMinimum_le_of_vectorDegree_le _ _ (fun x ↦ (hv x).le)
  have h := vectorDegree_le_maximalLogarithmicMinimum (bundle ∅ c hc hc1)
    ⟨(1,0), by simp⟩
  simpa only [hv, EReal.coe_zero] using h

/-- Actual rank-one restrictions have their generator's ambient vector degree. -/
theorem bundle_slope_restrict_line (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (W : Submodule ℚ Plane) (hW : Module.finrank ℚ W = 1)
    (x : {x : W // x ≠ 0}) :
    ((bundle s c hc hc1).restrictOfMeasurableBase W countingRegularity).slope
      countingRegularity countingArchimedeanNormalization =
      ((s.filter fun a ↦ x.val.val.2 = a * x.val.val.1).card : ℝ) * (-Real.log c) := by
  rw [AdelicVectorBundle.slope_eq_degree_of_finrank_one _ _ _ hW,
    AdelicVectorBundle.degree_eq_vectorDegree_of_finrank_one _ _ _ hW x,
    AdelicVectorBundle.vectorDegree_restrictOfMeasurableBase, bundle_vectorDegree]

private theorem restricted_line_slope_le (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (W : Submodule ℚ Plane)
    (hW : Module.finrank ℚ W = 1) :
    ((bundle s c hc hc1).restrictOfMeasurableBase W countingRegularity).slope
      countingRegularity countingArchimedeanNormalization ≤ -Real.log c := by
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (by rw [hW]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  rw [AdelicVectorBundle.slope_eq_degree_of_finrank_one _ _ _ hW,
    AdelicVectorBundle.degree_eq_vectorDegree_of_finrank_one _ _ _ hW ⟨x,hx⟩,
    AdelicVectorBundle.vectorDegree_restrictOfMeasurableBase]
  exact bundle_vectorDegree_le s c hc hc1 _

private theorem proper_nonzero_subspace_finrank (W : Submodule ℚ Plane)
    (hW : 0 < Module.finrank ℚ W) (ht : W ≠ ⊤) : Module.finrank ℚ W = 1 := by
  have hle : Module.finrank ℚ W ≤ 2 := by
    simpa only [finrank_plane] using W.finrank_le
  have hne : Module.finrank ℚ W ≠ 2 := by
    intro h
    exact ht (Submodule.eq_top_of_finrank_eq (h.trans finrank_plane.symm))
  omega

/-- The actual mean slope is half the original counting degree. -/
theorem bundle_slope (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (bundle s c hc hc1).slope countingRegularity countingArchimedeanNormalization =
      (s.card : ℝ) * (-Real.log c) / 2 := by
  rw [AdelicVectorBundle.slope, bundle_degree, finrank_plane]
  norm_num

/-- All actual nonzero subspaces, including the whole plane, compute the maximal slope. -/
theorem bundle_maximalSlope (s : Finset ℚ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hs : s.Nonempty) :
    (bundle s c hc hc1).maximalSlope countingRegularity countingArchimedeanNormalization =
      ((max (-Real.log c) ((s.card : ℝ) * (-Real.log c) / 2) : ℝ) : EReal) := by
  apply le_antisymm
  · apply AdelicVectorBundle.maximalSlope_le
    intro W hW
    by_cases ht : W = ⊤
    · rw [ht, AdelicVectorBundle.slope_restrict_top, bundle_slope]
      exact EReal.coe_le_coe_iff.mpr (le_max_right _ _)
    · exact EReal.coe_le_coe_iff.mpr ((restricted_line_slope_le s c hc hc1 W
        (proper_nonzero_subspace_finrank W hW ht)).trans (le_max_left _ _))
  · obtain ⟨a, ha⟩ := hs
    have hl := (bundle s c hc hc1).vectorDegree_le_maximalSlope countingRegularity
      countingArchimedeanNormalization ⟨(1,a), by simp⟩
    rw [bundle_vectorDegree_cheap s c hc hc1 a ha] at hl
    have hm := (bundle s c hc hc1).slope_le_maximalSlope countingRegularity
      countingArchimedeanNormalization (by rw [finrank_plane]; norm_num)
    rw [bundle_slope] at hm
    rcases le_total (-Real.log c) ((s.card : ℝ) * (-Real.log c) / 2) with h | h
    · rw [max_eq_right h]
      exact hm
    · rw [max_eq_left h]
      exact hl

/-- With at least two selected places the actual plane is mean-slope semistable. -/
theorem bundle_isMeanSlopeSemistable (s : Finset ℚ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hs : 2 ≤ s.card) :
    (bundle s c hc hc1).IsMeanSlopeSemistable countingRegularity
      countingArchimedeanNormalization := by
  apply (AdelicVectorBundle.isMeanSlopeSemistable_iff_maximalSlope_eq_slope _ _ _
    (by rw [finrank_plane]; norm_num)).mpr
  rw [bundle_maximalSlope s c hc hc1 (Finset.card_pos.mp (by omega)), bundle_slope]
  have hk : 0 ≤ -Real.log c := neg_nonneg.mpr (Real.log_nonpos hc.le hc1)
  have hn : (2 : ℝ) ≤ s.card := by exact_mod_cast hs
  rw [max_eq_right (by nlinarith : -Real.log c ≤ (s.card : ℝ) * (-Real.log c) / 2)]

/-- The empty finite truncation has actual maximal slope zero, not the rank-zero convention. -/
theorem bundle_maximalSlope_empty (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (bundle ∅ c hc hc1).maximalSlope countingRegularity countingArchimedeanNormalization =
      (0 : EReal) := by
  apply le_antisymm
  · apply AdelicVectorBundle.maximalSlope_le
    intro W hW
    by_cases ht : W = ⊤
    · rw [ht, AdelicVectorBundle.slope_restrict_top, bundle_slope]
      simp
    · have hr := proper_nonzero_subspace_finrank W hW ht
      have : Nontrivial W := Module.nontrivial_of_finrank_pos hW
      obtain ⟨x,hx⟩ := exists_ne (0 : W)
      rw [bundle_slope_restrict_line ∅ c hc hc1 W hr ⟨x,hx⟩]
      simp
  · have h := (bundle ∅ c hc hc1).slope_le_maximalSlope countingRegularity
      countingArchimedeanNormalization (by rw [finrank_plane]; norm_num)
    simpa only [bundle_slope, Finset.card_empty, Nat.cast_zero, zero_mul, zero_div,
      EReal.coe_zero] using h

/-- The literal cost chosen by source Remark 4.3.74 is within the generic interval. -/
theorem sourceCost_le_one : Real.exp (-1 : ℝ) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by norm_num)

/-- The actual source-cost finite bundle, retaining all produced analytic fields. -/
def sourceBundle (s : Finset ℚ) : AdelicVectorBundle countingCurve Plane :=
  bundle s (Real.exp (-1)) (Real.exp_pos _) sourceCost_le_one

/-- The source's actual degree is the number of selected counting atoms. -/
theorem sourceBundle_degree (s : Finset ℚ) :
    (sourceBundle s).degree countingRegularity countingArchimedeanNormalization = s.card := by
  rw [sourceBundle, bundle_degree]
  simp

/-- The actual source mean slope is cardinality divided by two. -/
theorem sourceBundle_slope (s : Finset ℚ) :
    (sourceBundle s).slope countingRegularity countingArchimedeanNormalization = s.card / 2 := by
  rw [sourceBundle, bundle_slope]
  simp

/-- Nonempty actual source truncations have first minimum one. -/
theorem sourceBundle_maximalLogarithmicMinimum (s : Finset ℚ) (hs : s.Nonempty) :
    (sourceBundle s).maximalLogarithmicMinimum = (1 : EReal) := by
  rw [sourceBundle, bundle_maximalLogarithmicMinimum _ _ _ _ hs]
  simp

/-- At least two selected places produce genuine semistable maximal slope `n/2`. -/
theorem sourceBundle_maximalSlope (s : Finset ℚ) (hs : 2 ≤ s.card) :
    (sourceBundle s).maximalSlope countingRegularity countingArchimedeanNormalization =
      (((s.card : ℝ) / 2 : ℝ) : EReal) := by
  have h := (AdelicVectorBundle.isMeanSlopeSemistable_iff_maximalSlope_eq_slope _ _ _
    (by rw [finrank_plane]; norm_num)).mp
      (bundle_isMeanSlopeSemistable s (Real.exp (-1)) (Real.exp_pos _) sourceCost_le_one hs)
  change (sourceBundle s).maximalSlope _ _ = ((sourceBundle s).slope _ _ : EReal) at h
  rw [sourceBundle_slope] at h
  exact h

/-- Distinct rational integer places give actual finite prefixes of every size. -/
def integerPlaces (n : ℕ) : Finset ℚ :=
  (Finset.range n).image (fun m : ℕ ↦ (m : ℚ))

/-- The finite prefix has its genuine cardinality. -/
theorem integerPlaces_card (n : ℕ) : (integerPlaces n).card = n := by
  rw [integerPlaces, Finset.card_image_of_injective _ Nat.cast_injective,
    Finset.card_range]

/-- A genuine positive-rank admissible actual bundle violates every prescribed finite level. -/
theorem exists_sourceBundle_violating_level (C : ℝ) :
    ∃ s : Finset ℚ, 2 ≤ s.card ∧
      (sourceBundle s).maximalLogarithmicMinimum + (C * Real.log 2 : ℝ) <
        (sourceBundle s).maximalSlope countingRegularity countingArchimedeanNormalization := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 : ℝ) (2 * (1 + C * Real.log 2)))
  have htwo : 2 ≤ n := by
    have h : (2 : ℝ) < n := (le_max_left _ _).trans_lt hn
    exact_mod_cast h.le
  refine ⟨integerPlaces n, by rw [integerPlaces_card]; exact htwo, ?_⟩
  rw [sourceBundle_maximalLogarithmicMinimum _
      (Finset.card_pos.mp (by rw [integerPlaces_card]; omega)),
    sourceBundle_maximalSlope _ (by rw [integerPlaces_card]; exact htwo), integerPlaces_card,
    ← EReal.coe_one, ← EReal.coe_add, EReal.coe_lt_coe_iff]
  have h : 2 * (1 + C * Real.log 2) < n := (le_max_right _ _).trans_lt hn
  linarith

/-- The actual proper rational counting curve has no finite ordinary Minkowski level. -/
theorem countingCurve_not_minkowski (C : ℝ) :
    ¬countingCurve.HasMinkowskiPropertyAtLevel.{0,0,0}
      countingRegularity countingArchimedeanNormalization C := by
  intro h
  obtain ⟨s, hs, hbad⟩ := exists_sourceBundle_violating_level C
  have hbound := h.maximalSlope_le (sourceBundle s)
    (by rw [finrank_plane]; norm_num)
    (truncatedFamily_isUltrametric s (Real.exp (-1)) (Real.exp_pos _) sourceCost_le_one)
  rw [finrank_plane, Nat.cast_ofNat] at hbound
  exact (not_lt_of_ge hbound) hbad

universe w

/-- The same actual source bundle in any vector-space universe, via an injective pullback. -/
def liftedSourceBundle (s : Finset ℚ) :
    AdelicVectorBundle countingCurve (ULift.{w} Plane) :=
  (sourceBundle s).pullback ULift.moduleEquiv.toLinearMap ULift.moduleEquiv.injective
    (by intro ℓ; exact measurable_of_countable _)

/-- The universe lift preserves the literal completed norm under canonical base change. -/
theorem liftedSourceBundle_norm (s : Finset ℚ) (a : countingCurve.Ω)
    (z : (countingCurve.ϕ a).Completion ⊗[ℚ] ULift.{w} Plane) :
    (liftedSourceBundle s).norm a z = (sourceBundle s).norm a
      ((ULift.moduleEquiv : ULift.{w} Plane ≃ₗ[ℚ] Plane).toLinearMap.baseChange
        (countingCurve.ϕ a).Completion z) := rfl

/-- The actual lifted vector space is still rank two. -/
theorem liftedSourceBundle_finrank : Module.finrank ℚ (ULift.{w} Plane) = 2 :=
  (ULift.moduleEquiv : ULift.{w} Plane ≃ₗ[ℚ] Plane).finrank_eq.trans finrank_plane

/-- Actual finite-place ultrametricity is transported through the injective base change. -/
theorem liftedSourceBundle_isUltrametric (s : Finset ℚ) :
    (liftedSourceBundle.{w} s).toNormFamily.IsUltrametric :=
  (truncatedFamily_isUltrametric s (Real.exp (-1)) (Real.exp_pos _) sourceCost_le_one).pullback
    ULift.moduleEquiv.toLinearMap ULift.moduleEquiv.injective

/-- The literal rational vector-degree integral agrees under the actual universe isometry. -/
theorem liftedSourceBundle_vectorDegree (s : Finset ℚ)
    (x : {x : ULift.{w} Plane // x ≠ 0}) :
    (liftedSourceBundle s).vectorDegree x =
      (sourceBundle s).vectorDegree ⟨x.val.down, by
        intro h
        exact x.property (ULift.ext _ _ h)⟩ := by
  rw [AdelicVectorBundle.vectorDegree, NormFamily.vectorDegree_eq_neg_integral,
    AdelicVectorBundle.vectorDegree, NormFamily.vectorDegree_eq_neg_integral]
  rfl

/-- The lifted first minimum has the same actual vector-degree upper bound. -/
theorem liftedSourceBundle_maximalLogarithmicMinimum_le (s : Finset ℚ) :
    (liftedSourceBundle.{w} s).maximalLogarithmicMinimum ≤ (1 : EReal) := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨x, _, hx⟩ := ((liftedSourceBundle.{w} s).le_finrank_degreeThresholdSpan_iff 1 t).mp ht
  have h : (liftedSourceBundle s).vectorDegree (x 0) ≤ 1 := by
    rw [liftedSourceBundle_vectorDegree]
    have h := bundle_vectorDegree_le s (Real.exp (-1)) (Real.exp_pos _) sourceCost_le_one
      ⟨(x 0).val.down, by intro h; exact (x 0).property (ULift.ext _ _ h)⟩
    simpa only [sourceBundle, Real.log_exp, neg_neg] using h
  exact EReal.coe_le_coe_iff.mpr ((hx 0).trans h)

/-- The actual maximal slope is preserved by the canonical completed universe isometry. -/
theorem liftedSourceBundle_maximalSlope (s : Finset ℚ) :
    (liftedSourceBundle.{w} s).maximalSlope countingRegularity countingArchimedeanNormalization =
      (sourceBundle s).maximalSlope countingRegularity countingArchimedeanNormalization := by
  apply AdelicVectorBundle.maximalSlope_eq_of_completed_isometry _ _
    (ULift.moduleEquiv : ULift.{w} Plane ≃ₗ[ℚ] Plane)
  intro a z
  rfl

/-- Every bundle universe contains an actual rank-two counterexample at every finite level. -/
theorem countingCurve_not_minkowski_universe (C : ℝ) :
    ¬countingCurve.HasMinkowskiPropertyAtLevel.{0,0,w}
      countingRegularity countingArchimedeanNormalization C := by
  intro h
  obtain ⟨s, hs, hbad⟩ := exists_sourceBundle_violating_level C
  have hb := h.maximalSlope_le (liftedSourceBundle.{w} s)
    (by rw [liftedSourceBundle_finrank]; norm_num) (liftedSourceBundle_isUltrametric s)
  rw [liftedSourceBundle_maximalSlope, liftedSourceBundle_finrank, Nat.cast_ofNat] at hb
  have hm : (liftedSourceBundle.{w} s).maximalLogarithmicMinimum ≤
      (sourceBundle s).maximalLogarithmicMinimum := by
    rw [sourceBundle_maximalLogarithmicMinimum s (Finset.card_pos.mp (by omega))]
    exact liftedSourceBundle_maximalLogarithmicMinimum_le s
  exact (not_lt_of_ge (hb.trans (add_le_add hm le_rfl))) hbad

/-- Every place of the literal counting curve is trivial, so its Archimedean mass is zero. -/
theorem countingCurve_archimedeanMass_eq_zero : countingCurve.v countingCurve.Ωinf = 0 := by
  have hempty : countingCurve.Ωinf = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := AbsoluteValue.isNonarchimedeanPlace_trivialPlace (K := ℚ)
    simp only [AbsoluteValue.IsNonarchimedeanPlace, AbsoluteValue.trivialPlace_out_eq] at h
    exact ha h
  rw [hempty, measure_empty]

/-- The actual counting curve has no finite strong level in any bundle universe. -/
theorem countingCurve_not_strongMinkowski_universe (C : ℝ) :
    ¬countingCurve.HasStrongMinkowskiPropertyAtLevel.{0,0,w}
      countingRegularity countingArchimedeanNormalization C := by
  intro h
  exact countingCurve_not_minkowski_universe C
    (h.minkowski_of_archimedeanMass_eq_zero countingCurve_archimedeanMass_eq_zero)

end
end ArakelovGeometry.MinkowskiCounting

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic
public import ArakelovGeometry.MeasureTheory.Function.ComplexEmbedding
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Compatible measurable Archimedean embeddings

The usual completed-field normalization is explicit. A single countable
subfield dense at infinite places suffices; no density at finite places is used.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.AdelicStructure

universe u v

variable {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)

/-- The canonical isometric complex embedding of a normalized infinite completion. -/
def archimedeanComplexEmbedding
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ωinf) :
    (S.ϕ ω.val).Completion →+* ℂ := by
  let := hS ω.val ω.property
  let := IsRCLikeNormedField.rclike (S.ϕ ω.val).Completion
  exact rclikeComplexEmbedding (S.ϕ ω.val).Completion

/-- This embedding preserves the prescribed completed absolute value. -/
@[simp]
theorem norm_archimedeanComplexEmbedding
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ωinf)
    (x : (S.ϕ ω.val).Completion) : ‖S.archimedeanComplexEmbedding hS ω x‖ = ‖x‖ := by
  let := hS ω.val ω.property
  let := IsRCLikeNormedField.rclike (S.ϕ ω.val).Completion
  exact norm_rclikeComplexEmbedding x

/-- Rational evaluations have the original absolute values of the adelic structure. -/
theorem norm_archimedeanComplexEmbedding_algebraMap
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ωinf) (a : K) :
    ‖S.archimedeanComplexEmbedding hS ω (algebraMap K (S.ϕ ω.val).Completion a)‖ =
      (S.ϕ ω.val) a := by
  rw [S.norm_archimedeanComplexEmbedding, S.norm_algebraMap_eq_absValue]

/-- A countable subfield dense only at the infinite places gives compatible
complex embeddings of the actual completions with measurable rational values. -/
theorem exists_measurable_archimedeanComplexEmbedding
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω ∈ S.Ωinf, S.IsDenseSubfieldAt K₀ ω) :
    ∃ σ : ∀ ω : S.Ωinf, (S.ϕ ω.val).Completion →+* ℂ,
      (∀ ω x, ‖σ ω x‖ = ‖x‖) ∧
        ∀ a : K, Measurable (fun ω : S.Ωinf =>
          σ ω (algebraMap K (S.ϕ ω.val).Completion a)) := by
  let e : S.Ωinf → K →+* ℂ := fun ω => (S.archimedeanComplexEmbedding hS ω).comp
    (algebraMap K (S.ϕ ω.val).Completion)
  have hm (a : K) : Measurable (fun ω => ‖e ω a‖) := by
    simpa only [e, RingHom.comp_apply, S.norm_archimedeanComplexEmbedding_algebraMap,
      Function.comp_def] using
      (S.measurable_absValue a).comp measurable_subtype_coe
  have hd (ω : S.Ωinf) (a : K) (ε : ℝ) (hε : 0 < ε) :
      ∃ b : K₀, ‖e ω (a - (b : K))‖ < ε := by
    obtain ⟨x, ⟨b, rfl⟩, hb⟩ := Metric.mem_closure_iff.mp
      (hK₀ ω.val ω.property (algebraMap K (S.ϕ ω.val).Completion a)) ε hε
    refine ⟨b, ?_⟩
    change ‖S.archimedeanComplexEmbedding hS ω
      (algebraMap K (S.ϕ ω.val).Completion (a - (b : K)))‖ < ε
    rw [S.norm_archimedeanComplexEmbedding, map_sub]
    simpa only [dist_eq_norm] using hb
  obtain ⟨c, hc⟩ := exists_measurable_conjugate_of_dense_subfield e hm K₀ hd
  refine ⟨fun ω => conjugateComplexEmbedding (S.archimedeanComplexEmbedding hS ω) (c ω),
    fun ω x => ?_, fun a => ?_⟩
  · rw [norm_conjugateComplexEmbedding, S.norm_archimedeanComplexEmbedding]
  · convert hc a using 1
    funext ω
    cases h : c ω <;> simp [e, conjugateComplexEmbedding, h]

/-- Reality of the whole completed image can be tested on one dense rational subfield. -/
theorem archimedean_real_iff_on_dense_subfield
    (σ : ∀ ω : S.Ωinf, (S.ϕ ω.val).Completion →+* ℂ)
    (hσ : ∀ ω x, ‖σ ω x‖ = ‖x‖) (K₀ : Subfield K)
    (hK₀ : ∀ ω ∈ S.Ωinf, S.IsDenseSubfieldAt K₀ ω) (ω : S.Ωinf) :
    (∀ x, (σ ω x).im = 0) ↔
      ∀ a : K₀, (σ ω (algebraMap K (S.ϕ ω.val).Completion (a : K))).im = 0 := by
  refine ⟨fun h a => h _, fun h x => ?_⟩
  exact (hK₀ ω.val ω.property).induction_on x
    (isClosed_eq (Complex.continuous_im.comp
      (isometry_complexEmbedding_of_norm (σ ω) (hσ ω)).continuous) continuous_const) h

/-- The real-completion locus is measurable: its defining vanishing condition
is the intersection of countably many measurable rational tests. -/
theorem measurableSet_archimedean_real_locus
    (σ : ∀ ω : S.Ωinf, (S.ϕ ω.val).Completion →+* ℂ)
    (hσ : ∀ ω x, ‖σ ω x‖ = ‖x‖)
    (hm : ∀ a : K, Measurable (fun ω : S.Ωinf =>
      σ ω (algebraMap K (S.ϕ ω.val).Completion a)))
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω ∈ S.Ωinf, S.IsDenseSubfieldAt K₀ ω) :
    MeasurableSet {ω : S.Ωinf | ∀ x, (σ ω x).im = 0} := by
  have he : {ω : S.Ωinf | ∀ x, (σ ω x).im = 0} =
      ⋂ a : K₀, {ω : S.Ωinf | (σ ω
        (algebraMap K (S.ϕ ω.val).Completion (a : K))).im = 0} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact S.archimedean_real_iff_on_dense_subfield σ hσ K₀ hK₀ ω
  rw [he]
  exact MeasurableSet.iInter fun a =>
    measurableSet_eq_fun (Complex.measurable_im.comp (hm (a : K))) measurable_const

/-- The complex-completion locus, where the completed embedding is onto the
complex numbers, is the measurable complement of the real locus. -/
theorem measurableSet_archimedean_complex_locus
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (σ : ∀ ω : S.Ωinf, (S.ϕ ω.val).Completion →+* ℂ)
    (hσ : ∀ ω x, ‖σ ω x‖ = ‖x‖)
    (hm : ∀ a : K, Measurable (fun ω : S.Ωinf =>
      σ ω (algebraMap K (S.ϕ ω.val).Completion a)))
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω ∈ S.Ωinf, S.IsDenseSubfieldAt K₀ ω) :
    MeasurableSet {ω : S.Ωinf | Function.Surjective (σ ω)} := by
  have he : {ω : S.Ωinf | Function.Surjective (σ ω)} =
      {ω : S.Ωinf | ∀ x, (σ ω x).im = 0}ᶜ := by
    ext ω
    let := hS ω.val ω.property
    let := IsRCLikeNormedField.rclike (S.ϕ ω.val).Completion
    exact complexEmbedding_surjective_iff (σ ω) (hσ ω)
  rw [he]
  exact (S.measurableSet_archimedean_real_locus σ hσ hm K₀ hK₀).compl

end ArakelovGeometry.AdelicStructure

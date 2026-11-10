/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.Analysis.NormedSpace.CountableNormEvaluation
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Measurable norm operations from a common countable subfield

Actual completed dual and quotient norms have countable rational evaluation
formulas. Their countable suprema and infima prove measurability under the
source's single common countable-density hypothesis.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w' wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ι : Type wι} [Fintype ι]

/-- The completed dual norm is a supremum over a fixed rational basis span.
The zero coefficient tuple contributes zero, so rank zero is included. -/
theorem dual_norm_eq_iSup_basisSubfield (ξ : NormFamily S E) (b : Module.Basis ι K E)
    (K₀ : Subfield K) (ω : S.Ω) (hK₀ : S.IsDenseSubfieldAt K₀ ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    ξ.dual.norm ω z = ⨆ c : ι → K₀,
      ‖dualBaseChangeEquiv K (S.ϕ ω).Completion E z
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c)‖ /
          ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  exact linearMapOperatorSeminorm_eq_sSup_of_denseRange
    (dualBaseChangeEquiv K (S.ϕ ω).Completion E z) _
    (ξ.denseRange_basisSubfieldMap b K₀ ω hK₀)

/-- For rational functionals the countable formula consists entirely of
absolute values and rational norm evaluations. -/
theorem dual_norm_rational_eq_iSup_basisSubfield (ξ : NormFamily S E)
    (b : Module.Basis ι K E) (K₀ : Subfield K) (ω : S.Ω)
    (hK₀ : S.IsDenseSubfieldAt K₀ ω) (ℓ : Module.Dual K E) :
    ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ) = ⨆ c : ι → K₀,
      (S.ϕ ω) (ℓ (basisSubfieldMap b K₀ c)) /
        ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) := by
  rw [ξ.dual_norm_eq_iSup_basisSubfield b K₀ ω hK₀]
  simp only [dualBaseChangeEquiv_tmul_apply_tmul, one_mul, S.norm_algebraMap_eq_absValue]

/-- A measurable family has a measurable dual when one countable subfield
is dense in all completed fields. -/
theorem IsMeasurable.dual_of_countable_dense_subfield {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable) (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω, S.IsDenseSubfieldAt K₀ ω) : ξ.dual.IsMeasurable := by
  intro ℓ
  let b := Module.finBasis K E
  have he : (fun ω => ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ)) =
      fun ω => ⨆ c : Fin (Module.finrank K E) → K₀,
        (S.ϕ ω) (ℓ (basisSubfieldMap b K₀ c)) /
          ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) :=
    funext fun ω => ξ.dual_norm_rational_eq_iSup_basisSubfield b K₀ ω (hK₀ ω) ℓ
  rw [he]
  exact Measurable.iSup fun c => (S.measurable_absValue _).div (hξ _)

/-- The source's existential common-subfield hypothesis supplies actual dual
measurability; no per-place choice of a different subfield is made. -/
theorem IsMeasurable.dual_of_common_countable_dense_subfield {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable) (hS : S.HasCommonCountableDenseSubfield) :
    ξ.dual.IsMeasurable := by
  obtain ⟨K₀, hcount, hK₀⟩ := hS
  let : Countable K₀ := hcount
  exact hξ.dual_of_countable_dense_subfield K₀ hK₀

variable {G : Type w'} [AddCommGroup G] [Module K G]

/-- The actual completed quotient norm is the infimum over the rational
basis span of the kernel translated by any chosen completed lift. -/
theorem pushforward_norm_eq_iInf_basisSubfield (ξ : NormFamily S E)
    (π : E →ₗ[K] G) (hπ : Function.Surjective π) (b : Module.Basis ι K π.ker)
    (K₀ : Subfield K) (ω : S.Ω) (hK₀ : S.IsDenseSubfieldAt K₀ ω)
    (s : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.pushforward π hπ).norm ω (π.baseChange (S.ϕ ω).Completion s) =
      ⨅ c : ι → K₀, ξ.norm ω
        (s + (1 : (S.ϕ ω).Completion) ⊗ₜ[K] ((basisSubfieldMap b K₀ c : π.ker) : E)) := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := (ξ.restrict π.ker).fibreNormedAddCommGroup ω
  let := (ξ.restrict π.ker).fibreNormedSpace ω
  let A : (ι → K₀) → ℝ := fun c => ξ.norm ω
    (s + (1 : (S.ϕ ω).Completion) ⊗ₜ[K] ((basisSubfieldMap b K₀ c : π.ker) : E))
  have hb : BddBelow (Set.range A) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨c, rfl⟩
    exact ξ.norm_nonneg ω _
  apply le_antisymm
  · apply le_csInf (Set.range_nonempty A)
    rintro _ ⟨c, rfl⟩
    have hk : π ((basisSubfieldMap b K₀ c : π.ker) : E) = 0 :=
      (basisSubfieldMap b K₀ c).property
    simpa only [map_add, LinearMap.baseChange_tmul, hk, TensorProduct.tmul_zero, add_zero] using
      ξ.pushforward_norm_le π hπ ω
        (s + (1 : (S.ϕ ω).Completion) ⊗ₜ[K] ((basisSubfieldMap b K₀ c : π.ker) : E))
  · apply (ξ.le_quotientSeminorm_iff π hπ ω _ _).mpr
    intro x hx
    have hk : x - s ∈
        (π.baseChange (S.ϕ ω).Completion).ker := by
      simp only [LinearMap.mem_ker, map_sub, hx, sub_self]
    rw [baseChange_ker π ω] at hk
    obtain ⟨t, ht⟩ := hk
    let j := π.ker.subtype.baseChange (S.ϕ ω).Completion
    have hc : Continuous (fun y => ξ.norm ω (s + j y)) :=
      (continuous_const.add (linearMapToNormedAddGroupHom j).continuous).norm
    have hd := (ξ.restrict π.ker).denseRange_basisSubfieldMap b K₀ ω hK₀
    have hbound : ∀ y, sInf (Set.range A) ≤ ξ.norm ω (s + j y) := by
      intro y
      apply hd.induction_on (p := fun y => sInf (Set.range A) ≤ ξ.norm ω (s + j y)) y
        (isClosed_le continuous_const hc)
      intro c
      simpa only [j, LinearMap.baseChange_tmul, Submodule.subtype_apply, A]
        using csInf_le hb ⟨c, rfl⟩
    have h := hbound t
    dsimp only [j] at h
    rw [ht, add_sub_cancel] at h
    exact h

/-- The quotient norm of a rational image is computed from the same
countable rational kernel span, now with rational translated evaluations. -/
theorem pushforward_norm_rational_eq_iInf_basisSubfield (ξ : NormFamily S E)
    (π : E →ₗ[K] G) (hπ : Function.Surjective π) (b : Module.Basis ι K π.ker)
    (K₀ : Subfield K) (ω : S.Ω) (hK₀ : S.IsDenseSubfieldAt K₀ ω) (s : E) :
    (ξ.pushforward π hπ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] π s) =
      ⨅ c : ι → K₀, ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K]
        (s + ((basisSubfieldMap b K₀ c : π.ker) : E))) := by
  simpa only [LinearMap.baseChange_tmul, ← TensorProduct.tmul_add] using
    ξ.pushforward_norm_eq_iInf_basisSubfield π hπ b K₀ ω hK₀
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] s)

/-- A measurable norm family has measurable quotients under one common
countable dense rational subfield. -/
theorem IsMeasurable.pushforward_of_countable_dense_subfield {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable) (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (K₀ : Subfield K) [Countable K₀] (hK₀ : ∀ ω, S.IsDenseSubfieldAt K₀ ω) :
    (ξ.pushforward π hπ).IsMeasurable := by
  intro z
  obtain ⟨s, rfl⟩ := hπ z
  let b := Module.finBasis K π.ker
  have he : (fun ω => (ξ.pushforward π hπ).norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] π s)) =
      fun ω => ⨅ c : Fin (Module.finrank K π.ker) → K₀,
        ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K]
          (s + ((basisSubfieldMap b K₀ c : π.ker) : E))) :=
    funext fun ω => ξ.pushforward_norm_rational_eq_iInf_basisSubfield π hπ b K₀ ω (hK₀ ω) s
  rw [he]
  exact Measurable.iInf fun c => hξ _

/-- The existential common-subfield hypothesis gives actual quotient measurability. -/
theorem IsMeasurable.pushforward_of_common_countable_dense_subfield {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable) (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (hS : S.HasCommonCountableDenseSubfield) : (ξ.pushforward π hπ).IsMeasurable := by
  obtain ⟨K₀, hcount, hK₀⟩ := hS
  let : Countable K₀ := hcount
  exact hξ.pushforward_of_countable_dense_subfield π hπ K₀ hK₀

/-- Canonical quotients by rational subspaces are measurable under the
same common-subfield hypothesis. -/
theorem IsMeasurable.quotient_of_common_countable_dense_subfield {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable) (F : Submodule K E) (hS : S.HasCommonCountableDenseSubfield) :
    (ξ.quotient F).IsMeasurable :=
  hξ.pushforward_of_common_countable_dense_subfield F.mkQ F.mkQ_surjective hS

/-- In finite dimension any second fibre norm is continuous for the first
norm's topology, also over a trivially normed complete field. -/
theorem continuous_fibreNorm_of_other (ξ η : NormFamily S E) (ω : S.Ω) :
    letI := ξ.fibreNormedAddCommGroup ω
    Continuous (η.norm ω) := by
  let := ξ.fibreNormedAddCommGroup ω
  obtain ⟨C, hC, h⟩ := ξ.exists_pos_norm_le_mul η ω
  let q : Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E) :=
    NNReal.mk C hC.le • ξ.norm ω
  have hc : Continuous q := by
    change Continuous (fun x => C * ξ.norm ω x)
    exact continuous_const.mul continuous_norm
  exact Seminorm.continuous_of_le hc h

/-- The local distance is computed on the same fixed rational basis span.
The zero tuple contributes zero, explicitly preserving the zero-rank convention. -/
theorem localDist_eq_iSup_basisSubfield (ξ η : NormFamily S E)
    (b : Module.Basis ι K E) (K₀ : Subfield K) (ω : S.Ω)
    (hK₀ : S.IsDenseSubfieldAt K₀ ω) :
    ξ.localDist η ω = ⨆ c : ι → K₀,
      |ξ.logNorm (basisSubfieldMap b K₀ c) ω - η.logNorm (basisSubfieldMap b K₀ c) ω| := by
  let := ξ.fibreNormedAddCommGroup ω
  let A : (ι → K₀) → ℝ := fun c =>
    |ξ.logNorm (basisSubfieldMap b K₀ c) ω - η.logNorm (basisSubfieldMap b K₀ c) ω|
  change ξ.localDist η ω = sSup (Set.range A)
  have hb : BddAbove (Set.range A) := by
    refine ⟨ξ.localDist η ω, ?_⟩
    rintro _ ⟨c, rfl⟩
    exact ξ.log_norm_sub_le_localDist η ω _
  have hC : 0 ≤ sSup (Set.range A) :=
    (abs_nonneg _).trans (le_csSup hb ⟨0, rfl⟩)
  have hcξ : Continuous (fun x : {x : (S.ϕ ω).Completion ⊗[K] E // x ≠ 0} =>
      Real.log (ξ.norm ω x)) :=
    (continuous_norm.comp continuous_subtype_val).log (fun x => (ξ.norm_pos ω x.property).ne')
  have hcη : Continuous (fun x : {x : (S.ϕ ω).Completion ⊗[K] E // x ≠ 0} =>
      Real.log (η.norm ω x)) :=
    ((ξ.continuous_fibreNorm_of_other η ω).comp continuous_subtype_val).log
      (fun x => (η.norm_pos ω x.property).ne')
  have hd := ξ.denseRange_basisSubfieldMap_nonzero b K₀ ω hK₀
  apply le_antisymm
  · apply ξ.localDist_le η ω
    intro x
    by_cases hx : x = 0
    · simpa only [hx, norm_zero, sub_self, abs_zero] using hC
    · exact hd.induction_on
        (p := fun x => |Real.log (ξ.norm ω x.val) - Real.log (η.norm ω x.val)| ≤
          sSup (Set.range A)) ⟨x, hx⟩
        (isClosed_le (hcξ.sub hcη).abs continuous_const)
        (fun c => le_csSup hb ⟨c.val, rfl⟩)
  · apply csSup_le (Set.range_nonempty A)
    rintro _ ⟨c, rfl⟩
    exact ξ.log_norm_sub_le_localDist η ω _

/-- Local distances of measurable norm families are measurable under a
single countable dense rational subfield. -/
theorem IsMeasurable.localDist_of_countable_dense_subfield {ξ η : NormFamily S E}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable) (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω, S.IsDenseSubfieldAt K₀ ω) : Measurable (ξ.localDist η) := by
  let b := Module.finBasis K E
  have he : ξ.localDist η = fun ω => ⨆ c : Fin (Module.finrank K E) → K₀,
      |ξ.logNorm (basisSubfieldMap b K₀ c) ω - η.logNorm (basisSubfieldMap b K₀ c) ω| :=
    funext fun ω => ξ.localDist_eq_iSup_basisSubfield η b K₀ ω (hK₀ ω)
  rw [he]
  apply Measurable.iSup
  intro c
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using
    ((hξ.logNorm (basisSubfieldMap b K₀ c)).sub (hη.logNorm (basisSubfieldMap b K₀ c))).norm

/-- The existential source hypothesis implies local-distance measurability. -/
theorem IsMeasurable.localDist_of_common_countable_dense_subfield {ξ η : NormFamily S E}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    (hS : S.HasCommonCountableDenseSubfield) : Measurable (ξ.localDist η) := by
  obtain ⟨K₀, hcount, hK₀⟩ := hS
  let : Countable K₀ := hcount
  exact hξ.localDist_of_countable_dense_subfield hη K₀ hK₀

private theorem sSup_range_eq_image_of_zero_off {α : Type*} [Nonempty α]
    (f : α → ℝ) (p : α → Prop) (hb : BddAbove (Set.range f))
    (hf : ∀ a, 0 ≤ f a) (hz : ∀ a, ¬p a → f a = 0) :
    sSup (Set.range f) = sSup (f '' {a | p a}) := by
  classical
  have hb' : BddAbove (f '' {a | p a}) := hb.mono (Set.image_subset_range _ _)
  by_cases hn : (f '' {a | p a}).Nonempty
  · have h0 : 0 ≤ sSup (f '' {a | p a}) := by
      obtain ⟨_, a, ha, rfl⟩ := hn
      exact (hf a).trans (le_csSup hb' ⟨a, ha, rfl⟩)
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty f)
      rintro _ ⟨a, rfl⟩
      by_cases ha : p a
      · exact le_csSup hb' ⟨a, ha, rfl⟩
      · simpa only [hz a ha] using h0
    · apply csSup_le hn
      rintro _ ⟨a, _, rfl⟩
      exact le_csSup hb ⟨a, rfl⟩
  · have he : Set.range f = {0} := Set.range_eq_singleton fun a =>
      hz a (fun ha => hn ⟨f a, a, ha, rfl⟩)
    rw [he, csSup_singleton, Set.not_nonempty_iff_eq_empty.mp hn, Real.sSup_empty]

/-- Source-exact dual formula over nonzero rational basis-span vectors.
The supremum is the empty real supremum, hence zero, in dimension zero. -/
theorem dual_norm_eq_sSup_nonzero_basisSubfield (ξ : NormFamily S E)
    (b : Module.Basis ι K E) (K₀ : Subfield K) (ω : S.Ω)
    (hK₀ : S.IsDenseSubfieldAt K₀ ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    ξ.dual.norm ω z = sSup
      ((fun c : ι → K₀ => ‖dualBaseChangeEquiv K (S.ϕ ω).Completion E z
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c)‖ /
          ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c)) ''
            {c | basisSubfieldMap b K₀ c ≠ 0}) := by
  rw [ξ.dual_norm_eq_iSup_basisSubfield b K₀ ω hK₀]
  apply sSup_range_eq_image_of_zero_off
  · refine ⟨ξ.dual.norm ω z, ?_⟩
    rintro _ ⟨c, rfl⟩
    by_cases hc : basisSubfieldMap b K₀ c = 0
    · simpa only [hc, TensorProduct.tmul_zero, map_zero, norm_zero, div_zero] using
        ξ.dual.norm_nonneg ω z
    · exact (div_le_iff₀ (ξ.norm_rational_pos ω hc)).mpr (ξ.norm_dual_apply_le ω z _)
  · intro c
    exact div_nonneg (_root_.norm_nonneg _) (ξ.norm_nonneg ω _)
  · intro c hc
    simp only [not_not] at hc
    simp only [hc, TensorProduct.tmul_zero, map_zero, div_zero]

/-- Source-exact local-distance formula on the nonzero countable rational
basis span, including its empty-supremum convention in rank zero. -/
theorem localDist_eq_sSup_nonzero_basisSubfield (ξ η : NormFamily S E)
    (b : Module.Basis ι K E) (K₀ : Subfield K) (ω : S.Ω)
    (hK₀ : S.IsDenseSubfieldAt K₀ ω) :
    ξ.localDist η ω = sSup
      ((fun c : ι → K₀ =>
        |ξ.logNorm (basisSubfieldMap b K₀ c) ω - η.logNorm (basisSubfieldMap b K₀ c) ω|) ''
          {c | basisSubfieldMap b K₀ c ≠ 0}) := by
  rw [ξ.localDist_eq_iSup_basisSubfield η b K₀ ω hK₀]
  apply sSup_range_eq_image_of_zero_off
  · refine ⟨ξ.localDist η ω, ?_⟩
    rintro _ ⟨c, rfl⟩
    exact ξ.log_norm_sub_le_localDist η ω _
  · exact fun _ => abs_nonneg _
  · intro c hc
    simp only [not_not] at hc
    simp only [hc, logNorm, TensorProduct.tmul_zero, norm_zero, sub_self, abs_zero]

end ArakelovGeometry.NormFamily

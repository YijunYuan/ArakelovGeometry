/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.CountableMeasurable
public import ArakelovGeometry.AdelicVectorBundle.OperatorNorm

/-!
# Measurable completed operator norms

A single dense rational coordinate set computes each actual completed operator
norm. The same set at every place proves measurability, with the zero map and
zero-dimensional source included. Nonzero rational maps have positive norm.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w' wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

/-- A nonzero rational map stays nonzero at every actual completed fibre. -/
theorem operatorNorm_pos (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) {f : E →ₗ[K] F} (hf : f ≠ 0) : 0 < ξ.operatorNorm η ω f := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext h)
  have hb := ξ.norm_baseChange_le_operatorNorm η ω f
    ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)
  simp only [LinearMap.baseChange_tmul] at hb
  have hp := lt_of_lt_of_le (η.norm_rational_pos ω hx) hb
  exact pos_of_mul_pos_left hp (ξ.norm_nonneg ω _)

/-- The local operator norm is a supremum of rational evaluation ratios.
Zero coordinate tuples contribute zero and require no exception. -/
theorem operatorNorm_eq_iSup_basisSubfield (ξ : NormFamily S E) (η : NormFamily S F)
    {ι : Type wι} [Fintype ι] (b : Module.Basis ι K E)
    (K₀ : Subfield K) (ω : S.Ω) (hK₀ : S.IsDenseSubfieldAt K₀ ω)
    (f : E →ₗ[K] F) :
    ξ.operatorNorm η ω f = ⨆ c : ι → K₀,
      η.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] f (basisSubfieldMap b K₀ c)) /
        ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := η.fibreNormedAddCommGroup ω
  let := η.fibreNormedSpace ω
  change linearMapOperatorSeminorm (f.baseChange (S.ϕ ω).Completion) = _
  rw [linearMapOperatorSeminorm_eq_sSup_of_denseRange
    (f.baseChange (S.ϕ ω).Completion) _ (ξ.denseRange_basisSubfieldMap b K₀ ω hK₀)]
  congr 2

/-- Common countable density proves actual operator-norm measurability. -/
theorem IsMeasurable.operatorNorm_of_common_countable_dense_subfield
    {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    (hS : S.HasCommonCountableDenseSubfield) (f : E →ₗ[K] F) :
    Measurable (fun ω => ξ.operatorNorm η ω f) := by
  obtain ⟨K₀, hcount, hdense⟩ := hS
  let : Countable K₀ := hcount
  simp_rw [operatorNorm_eq_iSup_basisSubfield ξ η (Module.finBasis K E) K₀ _ (hdense _) f]
  exact Measurable.iSup fun c => (hη _).div (hξ _)

/-- The exact two alternatives in the source imply operator-norm measurability. -/
theorem IsMeasurable.operatorNorm_of_discrete_or_countable
    {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsMeasurable) (hη : η.IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (f : E →ₗ[K] F) : Measurable (fun ω => ξ.operatorNorm η ω f) := by
  rcases hS with hS | hS
  · let := hS
    exact Measurable.of_discrete
  · exact hξ.operatorNorm_of_common_countable_dense_subfield hη hS f

end ArakelovGeometry.NormFamily

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldProjectiveGenericFibre
import ArakelovGeometry.NumberTheory.NumberFieldArithmeticProductBall
import Mathlib.Topology.DiscreteSubset

/-! # Effective sections of the original finite projective arithmetic module -/

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry

namespace NormFamily

variable {K E : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E]

/-- Rational vectors lying in the actual completed unit ball at every place. -/
def effectiveSections (ξ : NormFamily S E) : Set E :=
  {s | ∀ ω, ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] s) ≤ 1}

end NormFamily

namespace NumberFieldProjectiveGeneric

open AdelicStructure NumberFieldInvertibleGeneric NumberFieldFullLattice
  NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldArithmeticProductBall

variable {K : Type*} [Field K] [NumberField K]
  (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

/-- Effective sections in the original module, using the prescribed infinite norms. -/
def effectiveSections
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) : Set M :=
  {m | ∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf,
    η.norm ω ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion) ⊗ₜ[K]
      genericInclusion (K := K) M m) ≤ 1}

/-- The source logarithmic cardinality of the actual original effective-section set. -/
def logSectionCount
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) : ℝ :=
  Real.log (Nat.card (effectiveSections M η) : ℝ)

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

attribute [local instance] genericFiniteDimensional

omit [Module.Projective (𝓞 K) M] in
/-- The all-place condition is the literal original integral-image condition together
with the prescribed infinite norm inequalities. -/
theorem mem_adelicEffectiveSections_iff
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (s : K ⊗[𝓞 K] M) :
    s ∈ (fullLatticeAdelicBundle (genericImage (K := K) M)
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M)
      η).toNormFamily.effectiveSections ↔
      s ∈ genericImage (K := K) M ∧
        ∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf,
          η.norm ω ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion)
            ⊗ₜ[K] s) ≤ 1 := by
  let ξ := fullLatticeGaugeFamily (genericImage (K := K) M)
    (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η
  have hfinite := fullLatticeGaugeFamily_globalUnitBall_eq (genericImage (K := K) M)
    (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η
  change (∀ ω, ξ.norm ω (1 ⊗ₜ[K] s) ≤ 1) ↔ _
  constructor
  · intro hs
    refine ⟨?_, ?_⟩
    · change s ∈ (genericImage (K := K) M : Set (K ⊗[𝓞 K] M))
      rw [← hfinite]
      exact fun ω _ => hs ω
    · intro ω hω
      have hn : ω ∉ (normalizedNumberFieldAdelicStructure K).Ωfin := hω
      rw [← NumberFieldFullLattice.fullLatticeGaugeFamily_norm_not_finite
        (genericImage (K := K) M)
        (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) η ω hn]
      exact hs ω
  · rintro ⟨hs, hinf⟩ ω
    by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
    · have hf : s ∈ ξ.globalUnitBall := by rwa [hfinite]
      exact hf ω hω
    · change (fullLatticeGaugeFamily _ _ _ _).norm ω _ ≤ 1
      rw [NumberFieldFullLattice.fullLatticeGaugeFamily_norm_not_finite _ _ _ _ ω hω]
      exact hinf ω hω

omit [Module.Projective (𝓞 K) M] in
/-- The original generic inclusion preserves and detects the effective-section condition. -/
theorem genericInclusion_mem_effectiveSections_iff
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) (m : M) :
    genericInclusion (K := K) M m ∈
      (fullLatticeAdelicBundle (genericImage (K := K) M)
        (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M)
        η).toNormFamily.effectiveSections ↔ m ∈ effectiveSections M η := by
  rw [mem_adelicEffectiveSections_iff]
  exact and_iff_right ⟨m, rfl⟩

omit [Module.Projective (𝓞 K) M] in
/-- The original effective sections have exactly the canonical all-place section image. -/
theorem genericInclusion_image_effectiveSections_eq
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    genericInclusion (K := K) M '' effectiveSections M η =
      (fullLatticeAdelicBundle (genericImage (K := K) M)
        (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M)
        η).toNormFamily.effectiveSections := by
  ext s
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact (genericInclusion_mem_effectiveSections_iff M η m).mpr hm
  · intro hs
    obtain ⟨m, rfl⟩ := (mem_adelicEffectiveSections_iff M η s).mp hs |>.1
    exact ⟨m, (genericInclusion_mem_effectiveSections_iff M η m).mp hs, rfl⟩

/-- The original effective sections are canonically equivalent to all-place rational sections. -/
def effectiveSectionsEquiv
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    effectiveSections M η ≃
      (fullLatticeAdelicBundle (genericImage (K := K) M)
        (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M)
        η).toNormFamily.effectiveSections :=
  (Equiv.Set.imageOfInjOn (genericInclusion (K := K) M) (effectiveSections M η)
    (genericInclusion_injective (K := K) M).injOn).trans
      (Equiv.setCongr (genericInclusion_image_effectiveSections_eq M η))

omit [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- Zero is an actual original effective section. -/
theorem zero_mem_effectiveSections
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    (0 : M) ∈ effectiveSections M η := by
  intro ω _
  simp only [map_zero, TensorProduct.tmul_zero]
  exact zero_le_one

omit [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- Original effective sections are exactly the preimage of the actual product unit body. -/
theorem effectiveSections_eq_diagonal_preimage
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    effectiveSections M η = originalDiagonalMap (K := K) M ⁻¹' productBall η 1 := by
  ext m
  constructor
  · intro hm w
    exact hm _ (normalizedInfinitePlacePoint_mem_inf w)
  · intro hm ω hω
    obtain ⟨w, rfl⟩ := normalizedNumberFieldAdelicStructure_Ωinf_eq_range.le hω
    exact hm w

/-- Compactness of the actual unit body and discreteness of the original diagonal
produce finiteness, including the zero-rank case. -/
theorem finite_effectiveSections
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    (effectiveSections M η).Finite := by
  let := euclideanNormedAddCommGroup η
  let := euclideanNormedSpace η
  let := originalDiagonalMap_range_discrete (K := K) M η
  have hc := productBall_isCompact η (R := 1) zero_le_one
  have hf : (productBall η 1 ∩
      ((originalDiagonalMap (K := K) M).range : Set _)).Finite := by
    have hd : IsDiscrete ((originalDiagonalMap (K := K) M).range :
        Set (CompletedVectorProduct K (K ⊗[𝓞 K] M))) :=
      DiscreteTopology.isDiscrete
    apply Metric.finite_isBounded_inter_isClosed hd hc.isBounded
    exact AddSubgroup.isClosed_of_discrete
      (H := (originalDiagonalMap (K := K) M).range.toAddSubgroup)
  apply hf.of_injOn (f := originalDiagonalMap (K := K) M) ?_
    (originalDiagonalMap_injective (K := K) M).injOn
  intro m hm
  exact ⟨(Set.ext_iff.mp (effectiveSections_eq_diagonal_preimage M η) m).mp hm,
    ⟨m, rfl⟩⟩

/-- The canonical adelic section set is finite by its proved original-module correspondence. -/
theorem finite_adelicEffectiveSections
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    ((fullLatticeAdelicBundle (genericImage (K := K) M)
      (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M)
      η).toNormFamily.effectiveSections).Finite := by
  rw [← genericInclusion_image_effectiveSections_eq M η]
  exact (finite_effectiveSections M η).image _

/-- Cardinalities agree for the original source set and the canonical adelic set. -/
theorem card_effectiveSections_eq_adelic
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    Nat.card (effectiveSections M η) =
      Nat.card ((fullLatticeAdelicBundle (genericImage (K := K) M)
        (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M)
        η).toNormFamily.effectiveSections) :=
  Nat.card_congr (effectiveSectionsEquiv M η)

/-- The source logarithmic count is the actual all-place adelic count. -/
theorem logSectionCount_eq_adelic
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    logSectionCount M η =
      Real.log (Nat.card ((fullLatticeAdelicBundle (genericImage (K := K) M)
        (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M)
        η).toNormFamily.effectiveSections) : ℝ) := by
  rw [logSectionCount, card_effectiveSections_eq_adelic]

/-- The actual section count is positive because zero is present and finiteness is proved. -/
theorem card_effectiveSections_pos
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    0 < Nat.card (effectiveSections M η) := by
  let := (finite_effectiveSections M η).to_subtype
  let : Nonempty (effectiveSections M η) := ⟨⟨0, zero_mem_effectiveSections M η⟩⟩
  exact Nat.card_pos

/-- The source logarithmic section count is nonnegative. -/
theorem logSectionCount_nonneg
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M)) :
    0 ≤ logSectionCount M η := by
  apply Real.log_nonneg
  exact_mod_cast card_effectiveSections_pos M η

/-- Zero generic rank forces the original effective-section set to be exactly zero. -/
theorem effectiveSections_eq_singleton_of_finrank_zero
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 0) :
    effectiveSections M η = {0} := by
  ext m
  constructor
  · intro _
    apply Set.mem_singleton_iff.mpr
    apply genericInclusion_injective (K := K) M
    rw [map_zero]
    exact (finrank_zero_iff_forall_zero.mp hr) _
  · rintro rfl
    exact zero_mem_effectiveSections M η

/-- The zero-rank section cardinality is one. -/
theorem card_effectiveSections_eq_one_of_finrank_zero
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 0) :
    Nat.card (effectiveSections M η) = 1 := by
  rw [effectiveSections_eq_singleton_of_finrank_zero M η hr]
  exact Nat.card_unique

/-- The zero-rank source logarithmic section count is zero. -/
theorem logSectionCount_eq_zero_of_finrank_zero
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 0) : logSectionCount M η = 0 := by
  rw [logSectionCount, card_effectiveSections_eq_one_of_finrank_zero M η hr,
    Nat.cast_one, Real.log_one]

end NumberFieldProjectiveGeneric
end ArakelovGeometry

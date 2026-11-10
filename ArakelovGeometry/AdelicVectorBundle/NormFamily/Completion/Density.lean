/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Completion.Metric
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Approximation by finite modifications of norm families

The approximation mechanism in Chen–Moriwaki, Remark 4.1.36, for the
strongly dominated domain. Splicing uses the actual completed fibre norms.
No measurability of the original families is required: integrable majorants
control the upper-integral distance. The number-field lattice identification
is supplied separately.
-/

@[expose] public section

open MeasureTheory Filter

namespace ArakelovGeometry

attribute [local instance] Classical.propDecidable

universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]

namespace NormFamily

/-- Keep the first family's norms on a set of places, the second's elsewhere. -/
noncomputable def piecewise (ξ η : NormFamily S E) (T : Set S.Ω) : NormFamily S E where
  norm ω := if ω ∈ T then ξ.norm ω else η.norm ω
  norm_eq_zero_iff ω x := by
    classical
    split <;> first | exact ξ.norm_eq_zero_iff ω x | exact η.norm_eq_zero_iff ω x

@[simp]
theorem piecewise_norm (ξ η : NormFamily S E) (T : Set S.Ω) (ω : S.Ω) :
    (ξ.piecewise η T).norm ω = if ω ∈ T then ξ.norm ω else η.norm ω := by
  classical
  rfl

variable [FiniteDimensional K E]

/-- The distance from a splice to its first family is exactly the discarded tail. -/
theorem localDist_piecewise_left (ξ η : NormFamily S E) (T : Set S.Ω) (ω : S.Ω) :
    (ξ.piecewise η T).localDist ξ ω = Tᶜ.indicator (η.localDist ξ) ω := by
  classical
  by_cases h : ω ∈ T
  · simpa only [NormFamily.localDist, piecewise_norm, ite_eq_left h, Set.indicator_of_notMem
      (show ω ∉ Tᶜ by simpa using h)] using ξ.localDist_self ω
  · simp only [NormFamily.localDist, piecewise_norm, ite_eq_right h,
      Set.indicator_of_mem (show ω ∈ Tᶜ from h)]

/-- Strong domination is stable under arbitrary splicing of two strongly dominated families. -/
theorem IsStronglyDominated.piecewise {ξ η : NormFamily S E}
    (hξ : ξ.IsStronglyDominated) (hη : η.IsStronglyDominated)
    (hfin : S.v S.Ωinf < ⊤) (T : Set S.Ω) : (ξ.piecewise η T).IsStronglyDominated := by
  apply hη.of_localDist
  apply (hη.localDist hξ hfin).1.mono
  apply Eventually.of_forall
  intro ω
  classical
  by_cases h : ω ∈ T
  · simp only [NormFamily.localDist, piecewise_norm, ite_eq_left h, le_refl]
  · simpa only [NormFamily.localDist, piecewise_norm, ite_eq_right h] using
      (show η.localDist η ω ≤ η.localDist ξ ω by
        rw [η.localDist_self]; exact η.localDist_nonneg ξ ω)

end NormFamily

namespace StronglyDominatedNormFamily

variable [FiniteDimensional K E] [Fact (S.v S.Ωinf < ⊤)]

/-- Splicing as an operation on actual strongly dominated families. -/
noncomputable def piecewise (ξ η : StronglyDominatedNormFamily S E) (T : Set S.Ω) :
    StronglyDominatedNormFamily S E :=
  ⟨ξ.val.piecewise η.val T, ξ.property.piecewise η.property Fact.out T⟩

/-- Exhausting the places by measurable sets makes the splices converge in the source metric. -/
theorem tendsto_piecewise (ξ η : StronglyDominatedNormFamily S E)
    (T : ℕ → Set S.Ω) (hTm : ∀ n, MeasurableSet (T n))
    (hTex : ∀ ω, ∀ᶠ n in atTop, ω ∈ T n) :
    Tendsto (fun n ↦ ξ.piecewise η (T n)) atTop (nhds ξ) := by
  obtain ⟨A, hAi, hbound⟩ := (η.property.localDist ξ.property Fact.out).1
  let B : S.Ω → ℝ := fun ω ↦ |A ω|
  have hBi : Integrable B S.v := hAi.abs
  have hBp (ω) : 0 ≤ B ω := abs_nonneg _
  have hb : η.val.localDist ξ.val ≤ᵐ[S.v] B :=
    hbound.mono fun ω h ↦ h.trans (le_abs_self _)
  have ht : Tendsto (fun n ↦ ∫ ω, (T n)ᶜ.indicator B ω ∂S.v) atTop (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ ↦ (0 : ℝ)) B
      (fun n ↦ (hBi.indicator (hTm n).compl).aestronglyMeasurable) hBi
      (fun n ↦ Eventually.of_forall fun ω ↦ ?_)
      (Eventually.of_forall fun ω ↦ ?_)
    · simpa only [integral_zero] using h
    · classical
      by_cases hω : ω ∈ (T n)ᶜ
      · simp only [Set.indicator_of_mem hω, Real.norm_eq_abs, abs_of_nonneg (hBp ω), le_refl]
      · simp only [Set.indicator_of_notMem hω, norm_zero]; exact hBp ω
    · apply tendsto_const_nhds.congr'
      filter_upwards [hTex ω] with n hn
      exact (Set.indicator_of_notMem (show ω ∉ (T n)ᶜ by simpa using hn) B).symm
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ ht
  intro n
  have hi : (ξ.piecewise η (T n)).val.upperIntegralDist ξ.val ≤
      (∫ ω, (T n)ᶜ.indicator B ω ∂S.v : ℝ) := by
    apply sInf_le
    refine ⟨(T n)ᶜ.indicator B, hBi.indicator (hTm n).compl, ?_, rfl⟩
    filter_upwards [hb] with ω hω
    change (ξ.val.piecewise η.val (T n)).localDist ξ.val ω ≤ _
    rw [NormFamily.localDist_piecewise_left]
    by_cases hn : ω ∈ (T n)ᶜ
    · simpa only [Set.indicator_of_mem hn] using hω
    · simp only [Set.indicator_of_notMem hn, le_refl]
  rw [← dist_eq_upperIntegralDist] at hi
  exact EReal.coe_le_coe_iff.mp hi

variable [Countable S.Ω] [MeasurableSingletonClass S.Ω]

/-- Every strongly dominated family is a limit of finite modifications of any fixed one. -/
theorem exists_finite_modification_sequence (ξ η : StronglyDominatedNormFamily S E) :
    ∃ ζ : ℕ → StronglyDominatedNormFamily S E,
      (∀ n, ∃ T : Set S.Ω, T.Finite ∧ ∀ ω ∉ T, (ζ n).val.norm ω = η.val.norm ω) ∧
      Tendsto ζ atTop (nhds ξ) := by
  let T := (Set.countable_univ (α := S.Ω)).finiteExhaustion
  refine ⟨fun n ↦ ξ.piecewise η (T n), ?_, ?_⟩
  · intro n
    refine ⟨T n, T.finite n, fun ω hω ↦ ?_⟩
    exact ite_eq_right hω
  · apply tendsto_piecewise ξ η T (fun n ↦ (T.finite n).measurableSet)
    intro ω
    have hω : ω ∈ ⋃ n, T n := by rw [T.iUnion_eq]; trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
    exact eventually_atTop.mpr ⟨n, fun m hm ↦ T.mono hm hn⟩

/-- Finite modifications of a fixed strongly dominated family are dense. -/
theorem dense_finite_modifications (η : StronglyDominatedNormFamily S E) :
    Dense {ξ : StronglyDominatedNormFamily S E |
      ∃ T : Set S.Ω, T.Finite ∧ ∀ ω ∉ T, ξ.val.norm ω = η.val.norm ω} := by
  intro ξ
  obtain ⟨ζ, hζ, ht⟩ := exists_finite_modification_sequence ξ η
  exact mem_closure_of_tendsto ht (Eventually.of_forall hζ)

end StronglyDominatedNormFamily
end ArakelovGeometry

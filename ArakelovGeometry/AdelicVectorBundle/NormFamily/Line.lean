/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Norm families on lines

Exact rational scalar and dual formulas give the one-vector criteria for
measurability and domination in source Propositions 4.1.16 and 4.1.22.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]

variable [FiniteDimensional K E]

/-- Every norm family in dimension at most one is ultrametric at finite places.
Exact rank-one biduality transports the ultrametric completed dual norm. -/
theorem isUltrametric_of_finrank_le_one (ξ : NormFamily S E)
    (hr : Module.finrank K E ≤ 1) : ξ.IsUltrametric := by
  rw [← ξ.dual_dual_pullback_eq_of_finrank_le_one hr]
  exact ξ.dual.dual_isUltrametric.pullback
    (Module.Dual.eval K E) (Module.eval_apply_injective K)

omit [FiniteDimensional K E] in
/-- A nonzero rational vector generates a one-dimensional space. -/
theorem exists_smul_eq_of_finrank_one (hr : Module.finrank K E = 1)
    {x : E} (hx : x ≠ 0) (y : E) : ∃ a : K, a • x = y := by
  let b := FiniteDimensional.basisSingleton (Fin 1) hr x hx
  refine ⟨b.repr y 0, ?_⟩
  simpa only [Fin.sum_univ_one, b, FiniteDimensional.basisSingleton_apply] using b.sum_repr y

omit [FiniteDimensional K E] in
/-- On a line, measurability is tested on any one nonzero rational vector. -/
theorem isMeasurable_iff_norm_one_vector (ξ : NormFamily S E)
    (hr : Module.finrank K E = 1) {x : E} (hx : x ≠ 0) :
    ξ.IsMeasurable ↔
      Measurable (fun ω ↦ ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)) := by
  refine ⟨fun h ↦ h x, ?_⟩
  intro h y
  obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_one hr hx y
  simpa only [norm_rational_smul, Pi.mul_def] using
    (S.measurable_absValue a).mul h

/-- A line's completed dual norm is the evaluation divided by its generator norm. -/
theorem dual_norm_rational_eq_div (ξ : NormFamily S E) (hr : Module.finrank K E = 1)
    {x : E} (hx : x ≠ 0) (ℓ : Module.Dual K E) (ω : S.Ω) :
    ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ) =
      (S.ϕ ω) (ℓ x) / ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) := by
  let b := FiniteDimensional.basisSingleton (Fin 1) hr x hx
  rw [ξ.dual_norm_eq_div_of_basis ω (b.baseChange (S.ϕ ω).Completion)]
  simp only [Module.Basis.baseChange_apply, b, FiniteDimensional.basisSingleton_apply,
    dualBaseChangeEquiv_tmul_apply_tmul, one_mul, S.norm_algebraMap_eq_absValue]

/-- The dual of a measurable line family is measurable, with no density assumption. -/
theorem IsMeasurable.dual_of_finrank_one {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (hr : Module.finrank K E = 1) : ξ.dual.IsMeasurable := by
  have hn : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K E)
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  intro ℓ
  simpa only [ξ.dual_norm_rational_eq_div hr hx, Pi.div_def] using
    (S.measurable_absValue (ℓ x)).div (hξ x)

omit [FiniteDimensional K E] in
/-- On a line, upper domination is tested on any one nonzero rational vector. -/
theorem isUpperDominated_iff_logNorm_one_vector (ξ : NormFamily S E)
    (hr : Module.finrank K E = 1) {x : E} (hx : x ≠ 0) :
    ξ.IsUpperDominated ↔ HasIntegrableUpperBound (ξ.logNorm x) S.v := by
  refine ⟨fun h ↦ h x hx, ?_⟩
  intro h y hy
  obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_one hr hx y
  have ha : a ≠ 0 := by rintro rfl; simp at hy
  have he : ξ.logNorm (a • x) = (fun ω ↦ Real.log ((S.ϕ ω) a)) + ξ.logNorm x :=
    funext fun ω ↦ ξ.logNorm_smul ha hx ω
  rw [he]
  exact (integrable_hasIntegrableBounds (S.integrable_log a ha)).1.add h

omit [FiniteDimensional K E] in
/-- On a line, lower domination is tested on the same generator. -/
theorem isLowerDominated_iff_logNorm_one_vector (ξ : NormFamily S E)
    (hr : Module.finrank K E = 1) {x : E} (hx : x ≠ 0) :
    ξ.IsLowerDominated ↔ HasIntegrableLowerBound (ξ.logNorm x) S.v := by
  refine ⟨fun h ↦ h x hx, ?_⟩
  intro h y hy
  obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_one hr hx y
  have ha : a ≠ 0 := by rintro rfl; simp at hy
  have he : ξ.logNorm (a • x) = (fun ω ↦ Real.log ((S.ϕ ω) a)) + ξ.logNorm x :=
    funext fun ω ↦ ξ.logNorm_smul ha hx ω
  rw [he]
  exact (integrable_hasIntegrableBounds (S.integrable_log a ha)).2.add h

omit [FiniteDimensional K E] in
/-- A nonzero functional on a line cannot vanish on a generator. -/
theorem dual_apply_ne_zero_of_finrank_one (hr : Module.finrank K E = 1)
    {x : E} (hx : x ≠ 0) {ℓ : Module.Dual K E} (hℓ : ℓ ≠ 0) : ℓ x ≠ 0 := by
  intro he
  apply hℓ
  ext y
  obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_one hr hx y
  simp [he]

/-- A nonzero functional's log norm on a line is its scalar evaluation log
minus the generator log norm. -/
theorem dual_logNorm_eq_sub (ξ : NormFamily S E) (hr : Module.finrank K E = 1)
    {x : E} (hx : x ≠ 0) {ℓ : Module.Dual K E} (hℓ : ℓ ≠ 0) (ω : S.Ω) :
    ξ.dual.logNorm ℓ ω = Real.log ((S.ϕ ω) (ℓ x)) - ξ.logNorm x ω := by
  unfold NormFamily.logNorm
  rw [ξ.dual_norm_rational_eq_div hr hx,
    Real.log_div ((S.ϕ ω).pos (dual_apply_ne_zero_of_finrank_one hr hx hℓ)).ne'
      (ξ.norm_rational_pos ω hx).ne']

/-- A generator and its normalized dual generator have opposite log norms. -/
theorem dual_logNorm_eq_neg (ξ : NormFamily S E) (hr : Module.finrank K E = 1)
    {x : E} {ℓ : Module.Dual K E} (he : ℓ x = 1) (ω : S.Ω) :
    ξ.dual.logNorm ℓ ω = -ξ.logNorm x ω := by
  have hx : x ≠ 0 := by rintro rfl; simp at he
  have hℓ : ℓ ≠ 0 := by rintro rfl; simp at he
  rw [ξ.dual_logNorm_eq_sub hr hx hℓ, he, map_one, Real.log_one, zero_sub]

/-- Source Proposition 4.1.16: domination on a line is equivalent to two
integrable envelopes for the log norm of any one nonzero rational vector. -/
theorem isDominated_iff_logNorm_bounds (ξ : NormFamily S E)
    (hr : Module.finrank K E = 1) {x : E} (hx : x ≠ 0) :
    ξ.IsDominated ↔ HasIntegrableBounds (ξ.logNorm x) S.v := by
  refine ⟨fun h ↦ h.logNorm_bounds hx, ?_⟩
  intro h
  refine ⟨(ξ.isUpperDominated_iff_logNorm_one_vector hr hx).2 h.1, ?_⟩
  intro ℓ hℓ
  have he : ξ.dual.logNorm ℓ = (fun ω ↦ Real.log ((S.ϕ ω) (ℓ x))) +
      (fun ω ↦ -ξ.logNorm x ω) := by
    funext ω
    rw [ξ.dual_logNorm_eq_sub hr hx hℓ]
    rfl
  rw [he]
  exact (integrable_hasIntegrableBounds
    (S.integrable_log (ℓ x) (dual_apply_ne_zero_of_finrank_one hr hx hℓ))).1.add h.2.neg

/-- Existence of one dominated nonzero logarithmic evaluation suffices on a line. -/
theorem isDominated_iff_exists_logNorm_bounds (ξ : NormFamily S E)
    (hr : Module.finrank K E = 1) :
    ξ.IsDominated ↔ ∃ x : E, x ≠ 0 ∧ HasIntegrableBounds (ξ.logNorm x) S.v := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K E)
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨x, hx, h.logNorm_bounds hx⟩
  · rintro ⟨x, hx, h⟩
    exact (ξ.isDominated_iff_logNorm_bounds hr hx).2 h

/-- The all-nonzero-vector formulation of source Proposition 4.1.16. -/
theorem isDominated_iff_forall_logNorm_bounds (ξ : NormFamily S E)
    (hr : Module.finrank K E = 1) :
    ξ.IsDominated ↔ ∀ x : E, x ≠ 0 → HasIntegrableBounds (ξ.logNorm x) S.v := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K E)
  refine ⟨fun h x hx ↦ h.logNorm_bounds hx, ?_⟩
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  exact (ξ.isDominated_iff_logNorm_bounds hr hx).2 (h x hx)

end ArakelovGeometry.NormFamily

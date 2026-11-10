/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Bidual
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.Basic
import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.Bidual
import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.BidualHN
import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.DualConstancy
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Actual nearly orthogonal bases at the trivial place

The all-vector coefficient inequality bounds each original basis radius
by the constant actual bidual radius divided by the orthogonality factor.
Actual approximate spans construct such bases in the semistable case.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w v

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

namespace NormFamily

open AdelicStructure

open Classical in
/-- The literal all-vector coefficient inequality bounds every actual
basis radius; no ultrametricity of the original family is required. -/
theorem trivialSeminorm_basis_bounds_of_bidual_eq_const
    (ξ : NormFamily (singleTrivialPlace K) E) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≠ 0 → (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).trivialSeminorm x = c)
    {ι : Type v} (b : Module.Basis ι K E) {α : ℝ} (hα : 0 < α)
    (horth : ∀ x i, b.repr x i ≠ 0 → α * ξ.trivialSeminorm (b i) ≤ ξ.trivialSeminorm x)
    (i : ι) : c ≤ ξ.trivialSeminorm (b i) ∧ ξ.trivialSeminorm (b i) ≤ c / α := by
  have hlo : c ≤ ξ.trivialSeminorm (b i) := by
    rw [← h (b i) (b.ne_zero i), trivialSeminorm_apply, trivialSeminorm_apply]
    exact ξ.dual_dual_norm_eval_le PUnit.unit _
  have hp : 0 < ξ.trivialSeminorm (b i) := hc.trans_le hlo
  have hcoord : b.coord i ≠ 0 := by
    intro hz
    have he := congrArg (fun ℓ : Module.Dual K E ↦ ℓ (b i)) hz
    simp [Module.Basis.coord_apply] at he
  have hu := ξ.trivialSeminorm_dual_le_inv_of_ge_away_kernel (b.coord i)
    (mul_pos hα hp) (fun x hx ↦ horth x i (by
      simpa only [Module.Basis.coord_apply] using hx))
  rw [ξ.trivialSeminorm_dual_eq_inv_of_trivialSeminorm_bidual_eq_const
    hc h (b.coord i) hcoord] at hu
  have hm : α * ξ.trivialSeminorm (b i) ≤ c :=
    (inv_le_inv₀ hc (mul_pos hα hp)).mp hu
  exact ⟨hlo, (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using hm)⟩

open Classical in
/-- Genuine approximate-ball spans produce an actual finite basis and
the all-vector coefficient inequality, including the empty basis. -/
theorem exists_basis_orthogonal_of_trivialSeminorm_bidual_eq_const
    (ξ : NormFamily (singleTrivialPlace K) E) {c : ℝ} (hc : 0 < c)
    (h : ∀ x, x ≠ 0 → (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).trivialSeminorm x = c)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E,
      (∀ i, ξ.trivialSeminorm (b i) ≤ c / α) ∧
      ∀ x i, b.repr x i ≠ 0 → α * ξ.trivialSeminorm (b i) ≤ ξ.trivialSeminorm x := by
  have hca : c < c / α := by
    apply (lt_div_iff₀ hα).mpr
    nlinarith
  have hs : ⊤ ≤ Submodule.span K {y | ξ.trivialSeminorm y ≤ c / α} := by
    intro x _
    by_cases hx : x = 0
    · subst x
      exact Submodule.zero_mem _
    exact ξ.mem_span_of_trivialSeminorm_bidual_lt (div_pos hc hα) x
      (by rw [h x hx]; exact hca)
  let b₀ := Module.Basis.ofSpan hs
  let b := b₀.reindex (b₀.indexEquiv (Module.finBasis K E))
  have hb : ∀ i, ξ.trivialSeminorm (b i) ≤ c / α := by
    intro i
    apply Module.Basis.ofSpan_subset hs
    rw [← Module.Basis.range_reindex b₀ (b₀.indexEquiv (Module.finBasis K E))]
    exact Set.mem_range_self i
  refine ⟨b, hb, ?_⟩
  intro x i hi
  have hx : x ≠ 0 := by
    intro hz
    apply hi
    rw [hz, map_zero, Finsupp.zero_apply]
  have hlo : c ≤ ξ.trivialSeminorm x := by
    rw [← h x hx, trivialSeminorm_apply, trivialSeminorm_apply]
    exact ξ.dual_dual_norm_eval_le PUnit.unit _
  have hm := (le_div_iff₀ hα).mp (hb i)
  exact (show α * ξ.trivialSeminorm (b i) ≤ c from by
    simpa only [mul_comm] using hm).trans hlo

end NormFamily

namespace AdelicVectorBundle

open AdelicStructure

variable (V : AdelicVectorBundle (singleTrivialPlace K) E)
  (hS : DiscreteMeasurableSpace (singleTrivialPlace K).Ω ∨
    (singleTrivialPlace K).HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ (singleTrivialPlace K).Ωinf,
    IsRCLikeNormedField ((singleTrivialPlace K).ϕ ω).Completion)

open Classical in
/-- Every actual semistable bundle admits a genuine nearly orthogonal
basis, constructed from the original small vectors. -/
theorem exists_basis_orthogonal_of_isSemistable (hV : V.IsSemistable hS hN)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E,
      (∀ i, V.toNormFamily.trivialSeminorm (b i) ≤ Real.exp (-V.slope hS hN) / α) ∧
      ∀ x i, b.repr x i ≠ 0 →
        α * V.toNormFamily.trivialSeminorm (b i) ≤ V.toNormFamily.trivialSeminorm x := by
  obtain ⟨c, hc, h⟩ := (V.isSemistable_iff_exists_trivialSeminorm_bidual_eq_const
    hS hN hV.1).mp hV
  have hm := (V.slopes_eq_neg_log_of_trivialSeminorm_bidual_eq_const
    hS hN hc h hV.1).1
  rw [hm, neg_neg, Real.exp_log hc]
  exact V.toNormFamily.exists_basis_orthogonal_of_trivialSeminorm_bidual_eq_const hc h hα hα1

open Classical in
/-- Every genuine nearly orthogonal basis satisfies the stronger bound
`-log α`, and hence the universal source estimate (4.79). -/
theorem abs_log_trivialSeminorm_basis_sub_le_of_isSemistable
    (hV : V.IsSemistable hS hN) {ι : Type v} (b : Module.Basis ι K E)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (horth : ∀ x i, b.repr x i ≠ 0 →
      α * V.toNormFamily.trivialSeminorm (b i) ≤ V.toNormFamily.trivialSeminorm x)
    (i j : ι) :
    |Real.log (V.toNormFamily.trivialSeminorm (b i)) -
      Real.log (V.toNormFamily.trivialSeminorm (b j))| ≤ -Real.log α ∧
    |Real.log (V.toNormFamily.trivialSeminorm (b i)) -
      Real.log (V.toNormFamily.trivialSeminorm (b j))| ≤
        -(Module.finrank K E : ℝ) * Real.log α := by
  obtain ⟨c, hc, h⟩ := (V.isSemistable_iff_exists_trivialSeminorm_bidual_eq_const
    hS hN hV.1).mp hV
  obtain ⟨hi₀, hi₁⟩ := V.toNormFamily.trivialSeminorm_basis_bounds_of_bidual_eq_const
    hc h b hα horth i
  obtain ⟨hj₀, hj₁⟩ := V.toNormFamily.trivialSeminorm_basis_bounds_of_bidual_eq_const
    hc h b hα horth j
  have hli₀ := Real.log_le_log hc hi₀
  have hlj₀ := Real.log_le_log hc hj₀
  have hli₁ := Real.log_le_log (hc.trans_le hi₀) hi₁
  have hlj₁ := Real.log_le_log (hc.trans_le hj₀) hj₁
  rw [Real.log_div hc.ne' hα.ne'] at hli₁ hlj₁
  have hstrong : |Real.log (V.toNormFamily.trivialSeminorm (b i)) -
      Real.log (V.toNormFamily.trivialSeminorm (b j))| ≤ -Real.log α := by
    apply abs_le.mpr
    constructor <;> linarith
  refine ⟨hstrong, hstrong.trans ?_⟩
  have hr : (1 : ℝ) ≤ (Module.finrank K E : ℝ) := by
    exact_mod_cast hV.1
  have hlog : Real.log α ≤ 0 := Real.log_nonpos hα.le hα1.le
  nlinarith

open Classical in
/-- Actual bidual constancy gives zero variation on every basis,
and therefore the universal source estimate (4.80). -/
theorem abs_log_bidual_basis_sub_eq_zero_of_isSemistable
    (hV : V.IsSemistable hS hN) {ι : Type v} (b : Module.Basis ι K E)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (i j : ι) :
    |Real.log ((V.bidualOfMeasurableBase hS).toNormFamily.trivialSeminorm (b i)) -
      Real.log ((V.bidualOfMeasurableBase hS).toNormFamily.trivialSeminorm (b j))| = 0 ∧
    |Real.log ((V.bidualOfMeasurableBase hS).toNormFamily.trivialSeminorm (b i)) -
      Real.log ((V.bidualOfMeasurableBase hS).toNormFamily.trivialSeminorm (b j))| ≤
        -((Module.finrank K E : ℝ) + 1) * Real.log α := by
  obtain ⟨c, _, h⟩ := (V.isSemistable_iff_exists_trivialSeminorm_bidual_eq_const
    hS hN hV.1).mp hV
  rw [h (b i) (b.ne_zero i), h (b j) (b.ne_zero j), sub_self, abs_zero]
  refine ⟨rfl, ?_⟩
  have hr : (0 : ℝ) ≤ (Module.finrank K E : ℝ) := Nat.cast_nonneg _
  have hlog : Real.log α ≤ 0 := Real.log_nonpos hα.le hα1.le
  nlinarith

open Classical in
/-- On every genuine nonzero completed bidual vector the corrected
source error is exactly zero: logarithm plus the actual ordinary mean. -/
theorem log_bidual_norm_add_slope_eq_zero_of_isSemistable
    (hV : V.IsSemistable hS hN) (ω : (singleTrivialPlace K).Ω)
    (z : ((singleTrivialPlace K).ϕ ω).Completion ⊗[K] E) (hz : z ≠ 0) :
    Real.log ((V.bidualOfMeasurableBase hS).toNormFamily.norm ω z) + V.slope hS hN = 0 := by
  obtain ⟨c, hc, h⟩ := (V.isSemistable_iff_exists_trivialSeminorm_bidual_eq_const
    hS hN hV.1).mp hV
  have hm := (V.slopes_eq_neg_log_of_trivialSeminorm_bidual_eq_const
    hS hN hc h hV.1).1
  rw [(V.bidualOfMeasurableBase hS).toNormFamily.norm_eq_const_of_trivialSeminorm_eq_const
    h ω z hz, hm]
  exact add_neg_cancel _

end AdelicVectorBundle

end

end ArakelovGeometry

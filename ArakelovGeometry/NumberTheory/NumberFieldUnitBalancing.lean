/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Actual Dirichlet-unit balancing

The actual logarithmic unit lattice supplies a uniform covering bound in
the weighted logarithmic coordinates. No balancing assertion or bounded
fundamental domain is supplied as an extra hypothesis.
-/

open NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem
open scoped NumberField BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace ArakelovGeometry.NumberFieldUnitBalancing

variable (K : Type*) [Field K] [NumberField K]

/-- The real scalar extension of the actual integer logarithmic basis. -/
def logarithmicBasis : Module.Basis (Fin (NumberField.Units.rank K)) ℝ (logSpace K) :=
  (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)

theorem logarithmicBasis_span :
    Submodule.span ℤ (Set.range (logarithmicBasis K)) = unitLattice K :=
  (basisUnitLattice K).ofZLatticeBasis_span ℝ (unitLattice K)

/-- The sum of the norms of the actual real logarithmic basis vectors. -/
def coveringRadius : ℝ := ∑ i, ‖logarithmicBasis K i‖

theorem coveringRadius_nonneg : 0 ≤ coveringRadius K :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem coveringRadius_eq_zero_of_unitRank_eq_zero (hr : NumberField.Units.rank K = 0) :
    coveringRadius K = 0 := by
  unfold coveringRadius
  exact Finset.sum_eq_zero (fun i _ => False.elim (by simpa [hr] using i.isLt))

/-- Rounding the actual lattice basis produces an actual unit, uniformly
for all real weighted logarithmic vectors. -/
theorem exists_logarithmic_unit_covering (y : logSpace K) :
    ∃ u : (𝓞 K)ˣ, ‖y + logEmbedding K (Additive.ofMul u)‖ ≤ coveringRadius K := by
  classical
  let z := -ZSpan.floor (logarithmicBasis K) y
  have hz : (z : logSpace K) ∈ unitLattice K := by
    rw [← logarithmicBasis_span]
    exact z.property
  obtain ⟨a, _, ha⟩ := hz
  change logEmbedding K a = (z : logSpace K) at ha
  refine ⟨a.toMul, ?_⟩
  have h : ‖y + (z : logSpace K)‖ ≤ coveringRadius K := by
    simpa only [z, NegMemClass.coe_neg, add_comm, sub_eq_add_neg, coveringRadius,
      ZSpan.fract] using ZSpan.norm_fract_le (logarithmicBasis K) y
  change ‖y + logEmbedding K a‖ ≤ coveringRadius K
  rw [ha]
  exact h

/-- The average with the actual real/complex infinite-place multiplicities. -/
def weightedMean (x : InfinitePlace K → ℝ) : ℝ :=
  (∑ w, (mult w : ℝ) * x w) / (Module.finrank ℚ K : ℝ)

/-- A uniform bound for all infinite places, including the omitted place. -/
def balancingConstant : ℝ := (Fintype.card (InfinitePlace K) : ℝ) * coveringRadius K

theorem balancingConstant_nonneg : 0 ≤ balancingConstant K :=
  mul_nonneg (Nat.cast_nonneg _) (coveringRadius_nonneg K)

theorem balancingConstant_eq_zero_of_unitRank_eq_zero (hr : NumberField.Units.rank K = 0) :
    balancingConstant K = 0 := by
  rw [balancingConstant, coveringRadius_eq_zero_of_unitRank_eq_zero K hr, mul_zero]

theorem sum_weighted_unit_residual_eq_zero (x : InfinitePlace K → ℝ) (u : (𝓞 K)ˣ) :
    ∑ w, (mult w : ℝ) * (x w + Real.log (w u) - weightedMean K x) = 0 := by
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_mult_mul_log, add_zero, ← Finset.sum_mul, ← Nat.cast_sum, sum_mult_eq,
    weightedMean, mul_div_cancel₀ _ hd, sub_self]

omit [NumberField K] in
private theorem abs_le_mult_abs (w : InfinitePlace K) (r : ℝ) :
    |r| ≤ (mult w : ℝ) * |r| := by
  have hm : (1 : ℝ) ≤ mult w := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr mult_ne_zero)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (abs_nonneg r)

/-- Actual units balance every infinite-place coordinate around its genuine
weighted mean. The absolute estimate is stronger than the source's bound. -/
theorem exists_weighted_unit_balancing_abs (x : InfinitePlace K → ℝ) :
    ∃ u : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      |x w + Real.log (w u) - weightedMean K x| ≤ balancingConstant K := by
  classical
  let y : logSpace K := fun w => (mult w.val : ℝ) * (x w.val - weightedMean K x)
  obtain ⟨u, hu⟩ := exists_logarithmic_unit_covering K y
  let r : InfinitePlace K → ℝ := fun w => x w + Real.log (w u) - weightedMean K x
  have hother : ∀ w, w ≠ w₀ → |(mult w : ℝ) * r w| ≤ coveringRadius K := by
    intro w hw
    have h := (norm_le_pi_norm (y + logEmbedding K (Additive.ofMul u)) ⟨w, hw⟩).trans hu
    change |(mult w : ℝ) * (x w - weightedMean K x) +
      (mult w : ℝ) * Real.log (w u)| ≤ coveringRadius K at h
    have heq : (mult w : ℝ) * r w = (mult w : ℝ) * (x w - weightedMean K x) +
        (mult w : ℝ) * Real.log (w u) := by dsimp [r]; ring
    rwa [← heq] at h
  have hC := coveringRadius_nonneg K
  have hCB : coveringRadius K ≤ balancingConstant K := by
    have hn : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) :=
      Nat.one_le_cast.mpr Fintype.card_pos
    simpa only [one_mul, balancingConstant] using mul_le_mul_of_nonneg_right hn hC
  refine ⟨u, fun w => ?_⟩
  change |r w| ≤ balancingConstant K
  by_cases hw : w = w₀
  · subst w
    have hsum := sum_weighted_unit_residual_eq_zero K x u
    change ∑ w, (mult w : ℝ) * r w = 0 at hsum
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsum
    have hsumBound : |∑ w : {w : InfinitePlace K // w ≠ w₀},
        (mult w.val : ℝ) * r w.val| ≤ balancingConstant K := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h := Finset.sum_le_sum (s := Finset.univ)
        (fun (w : {w : InfinitePlace K // w ≠ w₀}) _ => hother w.val w.property)
      refine h.trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Fintype.card_subtype_le (fun w : InfinitePlace K => w ≠ w₀))) hC
    have heq : (mult (w₀ : InfinitePlace K) : ℝ) * r w₀ =
        -(∑ w : {w : InfinitePlace K // w ≠ w₀}, (mult w.val : ℝ) * r w.val) := by
      linarith
    have hweighted : |(mult (w₀ : InfinitePlace K) : ℝ) * r w₀| ≤
        balancingConstant K := by rw [heq, abs_neg]; exact hsumBound
    exact (abs_le_mult_abs K w₀ (r w₀)).trans (by simpa only [abs_mul, Nat.abs_cast] using
      hweighted)
  · have hweighted : (mult w : ℝ) * |r w| ≤ coveringRadius K := by
      simpa only [abs_mul, Nat.abs_cast] using hother w hw
    exact (abs_le_mult_abs K w (r w)).trans (hweighted.trans hCB)

theorem exists_weighted_unit_balancing (x : InfinitePlace K → ℝ) :
    ∃ u : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      x w + Real.log (w u) ≤ weightedMean K x + balancingConstant K := by
  obtain ⟨u, hu⟩ := exists_weighted_unit_balancing_abs K x
  refine ⟨u, fun w => ?_⟩
  have h := (le_abs_self _).trans (hu w)
  linarith

end ArakelovGeometry.NumberFieldUnitBalancing

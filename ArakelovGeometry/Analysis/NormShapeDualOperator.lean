/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.NormShapeDual
import ArakelovGeometry.Analysis.ArchimedeanDual
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.RCLike.Lemmas

/-!
# The actual Archimedean operator dual of a profile sum

Finite-dimensional unit-ball attainment and scalar phase alignment produce
the exact polar-profile formula, including zero-dimensional factors.
-/

noncomputable section

namespace ArakelovGeometry
namespace NormShape

variable (ψ : NormShape)

private theorem dual_perspective_term {A B : ℝ} (h : A + B ≠ 0)
    (u : Set.Icc (0 : ℝ) 1) :
    (A + B) * ψ.dualTerm (A / (A + B)) u =
      (A * u.val + B * (1 - u.val)) / ψ.toFun u.val := by
  unfold dualTerm
  field_simp
  ring

/-- The scalar polar perspective is the least nonnegative bound for the affine numerator. -/
theorem dual_perspective_le {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ∀ u : Set.Icc (0 : ℝ) 1, A * u.val + B * (1 - u.val) ≤ C * ψ.toFun u.val) :
    ψ.dual.perspective A B ≤ C := by
  by_cases hs : A + B = 0
  · have hA0 : A = 0 := by linarith
    have hB0 : B = 0 := by linarith
    simpa [hA0, hB0] using hC
  have hspos : 0 < A + B := lt_of_le_of_ne (add_nonneg hA hB) (Ne.symm hs)
  change (A + B) * ψ.dualValue (A / (A + B)) ≤ C
  rw [mul_comm]
  apply (le_div_iff₀ hspos).mp
  apply ψ.dualValue_le
  intro u
  apply (le_div_iff₀ hspos).mpr
  rw [mul_comm, ψ.dual_perspective_term hs u]
  exact (div_le_iff₀ (ψ.pos u.property)).mpr (h u)

theorem weighted_le_dual_perspective_mul {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (u : Set.Icc (0 : ℝ) 1) :
    A * u.val + B * (1 - u.val) ≤ ψ.dual.perspective A B * ψ.toFun u.val := by
  by_cases hs : A + B = 0
  · have hA0 : A = 0 := by linarith
    have hB0 : B = 0 := by linarith
    simp [hA0, hB0]
  have h := mul_le_mul_of_nonneg_left
    (ψ.dualTerm_le_dualValue (A / (A + B)) u) (add_nonneg hA hB)
  rw [ψ.dual_perspective_term hs u] at h
  exact (div_le_iff₀ (ψ.pos u.property)).mp h

/-- The exact numerical Hölder inequality for a profile and its polar. -/
theorem pairing_le_dual_perspective_mul {A B a b : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    A * a + B * b ≤ ψ.dual.perspective A B * ψ.perspective a b := by
  by_cases hs : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  have hspos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
  let u : Set.Icc (0 : ℝ) 1 := ⟨a / (a + b), div_nonneg ha hspos.le,
    (div_le_one hspos).mpr (by linarith)⟩
  have h := mul_le_mul_of_nonneg_right (ψ.weighted_le_dual_perspective_mul hA hB u) hspos.le
  have hleft : (A * u.val + B * (1 - u.val)) * (a + b) = A * a + B * b := by
    dsimp [u]
    field_simp
    ring
  have hright : ψ.dual.perspective A B * ψ.toFun u.val * (a + b) =
      ψ.dual.perspective A B * ψ.perspective a b := by
    dsimp [u, perspective]
    ring
  rwa [hleft, hright] at h

end NormShape

variable {L V : Type*} [RCLike L] [NormedAddCommGroup V] [NormedSpace L V]
  [FiniteDimensional L V]

/-- A finite-dimensional functional attains its norm as a nonnegative scalar on the unit ball. -/
theorem exists_unitBall_apply_eq_operatorNorm (f : V →ₗ[L] L) :
    ∃ x : V, ‖x‖ ≤ 1 ∧ f x = (linearMapOperatorSeminorm f : L) := by
  let : ProperSpace L := FiniteDimensional.proper ℝ L
  let : ProperSpace V := FiniteDimensional.proper L V
  let g := LinearMap.toContinuousLinearMap f
  have hop : linearMapOperatorSeminorm f = ‖g‖ :=
    linearMapOperatorSeminorm_coe_continuousLinearMap g
  by_cases hg : ‖g‖ = 0
  · refine ⟨0, by simp, ?_⟩
    simp [hop, hg]
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall (0 : V) 1).exists_isMaxOn
    (by exact ⟨0, by simp⟩) g.continuous.norm.continuousOn
  have hxnorm : ‖x‖ ≤ 1 := by simpa using hx
  have hnorm : ‖g x‖ = ‖g‖ := by
    apply le_antisymm
    · simpa using g.le_opNorm_of_le hxnorm
    · apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
      intro y hy
      exact hmax (by simpa using hy.le)
  have hgx : g x ≠ 0 := norm_ne_zero_iff.mp (hnorm ▸ hg)
  let c : L := (‖g‖ : L) / g x
  have hc : ‖c‖ = 1 := by
    simp only [c, norm_div, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), hnorm]
    exact div_self hg
  refine ⟨c • x, ?_, ?_⟩
  · simpa only [norm_smul, hc, one_mul] using hxnorm
  · rw [map_smul, smul_eq_mul]
    change c * g x = (linearMapOperatorSeminorm f : L)
    rw [hop]
    exact div_mul_cancel₀ _ hgx

/-- Scaled nonnegative norm attainment includes zero functionals and zero-dimensional spaces. -/
theorem exists_ball_apply_eq_operatorNorm (f : V →ₗ[L] L) {r : ℝ} (hr : 0 ≤ r) :
    ∃ x : V, ‖x‖ ≤ r ∧ f x = ((r * linearMapOperatorSeminorm f : ℝ) : L) := by
  obtain ⟨x, hx, hfx⟩ := exists_unitBall_apply_eq_operatorNorm f
  refine ⟨(r : L) • x, ?_, ?_⟩
  · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hr]
    exact mul_le_of_le_one_right hr hx
  · rw [map_smul, smul_eq_mul, hfx, RCLike.ofReal_mul]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace L W] [FiniteDimensional L W]

/-- The actual operator-dual ratio supremum of a profile product is its polar perspective. -/
theorem sSup_profile_dual_ratio (ψ : NormShape) (f : V →ₗ[L] L) (g : W →ₗ[L] L) :
    sSup (Set.range fun z : V × W ↦
      ‖f z.1 + g z.2‖ / ψ.perspective ‖z.1‖ ‖z.2‖) =
      ψ.dual.perspective (linearMapOperatorSeminorm f) (linearMapOperatorSeminorm g) := by
  let A := linearMapOperatorSeminorm f
  let B := linearMapOperatorSeminorm g
  let C := ψ.dual.perspective A B
  let R := Set.range fun z : V × W ↦ ‖f z.1 + g z.2‖ / ψ.perspective ‖z.1‖ ‖z.2‖
  have hA : 0 ≤ A := apply_nonneg _ _
  have hB : 0 ≤ B := apply_nonneg _ _
  have hC : 0 ≤ C := ψ.dual.perspective_nonneg hA hB
  have happly (z : V × W) : ‖f z.1 + g z.2‖ ≤ C * ψ.perspective ‖z.1‖ ‖z.2‖ := by
    exact (norm_add_le _ _).trans ((add_le_add
      (norm_linearMap_apply_le f z.1) (norm_linearMap_apply_le g z.2)).trans
        (ψ.pairing_le_dual_perspective_mul hA hB (norm_nonneg _) (norm_nonneg _)))
  have hratio (z : V × W) :
      ‖f z.1 + g z.2‖ / ψ.perspective ‖z.1‖ ‖z.2‖ ≤ C := by
    by_cases hz : ψ.perspective ‖z.1‖ ‖z.2‖ = 0
    · simpa only [hz, div_zero] using hC
    · exact (div_le_iff₀ (lt_of_le_of_ne
        (ψ.perspective_nonneg (norm_nonneg _) (norm_nonneg _)) (Ne.symm hz))).mpr (happly z)
  have hbdd : BddAbove R := ⟨C, by rintro _ ⟨z, rfl⟩; exact hratio z⟩
  have hR0 : 0 ≤ sSup R := le_csSup hbdd ⟨0, by simp⟩
  have heval (z : V × W) : ‖f z.1 + g z.2‖ ≤ sSup R * ψ.perspective ‖z.1‖ ‖z.2‖ := by
    by_cases hz : z = 0
    · simp [hz]
    have hpos : 0 < ψ.perspective ‖z.1‖ ‖z.2‖ := by
      apply lt_of_le_of_ne (ψ.perspective_nonneg (norm_nonneg _) (norm_nonneg _))
      intro he
      have he' := (ψ.perspective_eq_zero_iff (norm_nonneg _) (norm_nonneg _)).mp he.symm
      exact hz (Prod.ext (norm_eq_zero.mp he'.1) (norm_eq_zero.mp he'.2))
    exact (div_le_iff₀ hpos).mp (le_csSup hbdd (Set.mem_range_self z))
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨z, rfl⟩; exact hratio z)
  · apply ψ.dual_perspective_le hA hB hR0
    intro u
    obtain ⟨x, hx, hfx⟩ := exists_ball_apply_eq_operatorNorm f u.property.1
    obtain ⟨y, hy, hgy⟩ := exists_ball_apply_eq_operatorNorm g (sub_nonneg.mpr u.property.2)
    have hval : ‖f x + g y‖ = A * u.val + B * (1 - u.val) := by
      rw [hfx, hgy, ← RCLike.ofReal_add, RCLike.norm_ofReal,
        abs_of_nonneg (add_nonneg (mul_nonneg u.property.1 hA)
          (mul_nonneg (sub_nonneg.mpr u.property.2) hB))]
      ring
    have hp := ψ.perspective_mono (norm_nonneg x) (norm_nonneg y) hx hy
    have hp' : ψ.perspective u.val (1 - u.val) = ψ.toFun u.val := by
      simp [NormShape.perspective]
    have h := heval (x, y)
    rw [hval] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hp.trans_eq hp') hR0)

end ArakelovGeometry

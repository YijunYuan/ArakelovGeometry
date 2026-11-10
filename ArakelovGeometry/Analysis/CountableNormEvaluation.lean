/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.LinearMapBound

/-!
# Norm evaluations on dense ranges

Operator norms can be computed from any dense range, using continuity of the
norm inequality rather than continuity of a quotient at zero. This retains
zero-dimensional spaces and trivially normed complete fields.
-/

@[expose] public section

namespace ArakelovGeometry

variable {L V W α : Type*} [NormedField L] [CompleteSpace L]
  [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V]
  [SeminormedAddCommGroup W] [NormedSpace L W]

/-- A bound on a dense range bounds the operator norm. The continuous
inequality includes zero, so no punctured-space argument is needed. -/
theorem linearMapOperatorSeminorm_le_of_denseRange (f : V →ₗ[L] W)
    (d : α → V) (hd : DenseRange d) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a, ‖f (d a)‖ ≤ C * ‖d a‖) : linearMapOperatorSeminorm f ≤ C := by
  apply linearMapOperatorSeminorm_le f hC
  intro x
  exact hd.induction_on (p := fun y => ‖f y‖ ≤ C * ‖y‖) x
    (isClosed_le (linearMapToNormedAddGroupHom f).continuous.norm
      (continuous_const.mul continuous_norm)) h

/-- The operator norm is a supremum over any dense range. A zero vector in
the range contributes zero, and the formula also covers the zero space. -/
theorem linearMapOperatorSeminorm_eq_sSup_of_denseRange (f : V →ₗ[L] W)
    (d : α → V) (hd : DenseRange d) :
    linearMapOperatorSeminorm f = sSup (Set.range fun a => ‖f (d a)‖ / ‖d a‖) := by
  let : Nonempty α := hd.nonempty
  have hb : BddAbove (Set.range fun a => ‖f (d a)‖ / ‖d a‖) := by
    refine ⟨linearMapOperatorSeminorm f, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact (linearMapToNormedAddGroupHom f).ratio_le_opNorm (d a)
  have hC : 0 ≤ sSup (Set.range fun a => ‖f (d a)‖ / ‖d a‖) := by
    obtain ⟨a⟩ := ‹Nonempty α›
    exact (div_nonneg (norm_nonneg _) (norm_nonneg _)).trans (le_csSup hb ⟨a, rfl⟩)
  apply le_antisymm
  · apply linearMapOperatorSeminorm_le_of_denseRange f d hd hC
    intro a
    by_cases ha : d a = 0
    · simp [ha]
    · exact (div_le_iff₀ (norm_pos_iff.mpr ha)).mp (le_csSup hb ⟨a, rfl⟩)
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨a, rfl⟩
    exact (linearMapToNormedAddGroupHom f).ratio_le_opNorm (d a)

/-- Removing the zero fibre from the source of a dense range leaves a dense
range in the punctured normed space; in rank zero the target is empty. -/
theorem denseRange_subtype_ne_zero (d : α → V) (hd : DenseRange d) :
    DenseRange (fun a : {a // d a ≠ 0} => (⟨d a, a.property⟩ : {x : V // x ≠ 0})) := by
  apply Metric.denseRange_iff.mpr
  intro x r hr
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp hd x.val (min r ‖x.val‖)
    (lt_min hr (norm_pos_iff.mpr x.property))
  have hda : d a ≠ 0 := by
    intro hz
    have he := ha.trans_le (min_le_right _ _)
    rw [hz, dist_zero_right] at he
    exact (lt_irrefl _ he)
  exact ⟨⟨a, hda⟩, ha.trans_le (min_le_left _ _)⟩

end ArakelovGeometry

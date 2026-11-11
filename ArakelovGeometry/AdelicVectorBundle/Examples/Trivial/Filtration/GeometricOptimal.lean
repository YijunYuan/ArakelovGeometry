/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Instability
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Optimal

/-!
# Actual original-field global optimizers from geometric instability

This is the binary implication of Chen–Moriwaki Theorem 5.4.3 used on Bost page 31.
The hypothesis is the existing A2 geometric semistability predicate for the same
surjective positive-rank quotient. The checked instability theorem produces an
actual centered negative pair over the original characteristic-zero field, and
the conditional optimizer theorem then constructs a unit negative global optimizer
over that field. Expectations and self-pairings retain reciprocal-rank normalization.

This proves neither the full CM (5.13) nor the arithmetic HN induction or Bost
Theorem 1.1. Only the binary geometric-to-optimizer implication is asserted;
no rationality of real weights or finite degree of the algebraic closure is required.
-/

@[expose] public section

open Module ArakelovGeometry ArakelovGeometry.InvariantTheory
open scoped TensorProduct

namespace Submodule

universe u

variable {K E F Q : Type u} [Field K] [CharZero K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Nontrivial E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F] [Nontrivial F]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Nontrivial Q]

/-- Bost page 31's actual unit negative GLOBAL optimizer from the A2 geometric
nonsemistability hypothesis on this same quotient. This is the binary existence
implication of CM Theorem 5.4.3, not its full variational inequality (5.13).
The comparison ranges over all actual centered finite real filtrations over the
original characteristic-zero field, not only over one coordinate presentation. -/
theorem exists_normalized_tensor_quotient_optimizer_of_not_geometricallySemistable
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q) (hQ : 0 < finrank K Q)
    (hns : ¬ IsGeometricallySemistableTensorQuotient (BoolTensorFactors E F)
      (q.comp (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap)) :
    ∃ (P : ℝ → Submodule K E) (R : ℝ → Submodule K F),
      (Antitone P ∧ (∃ t, P t = ⊥) ∧ (∃ t, P t = ⊤) ∧
        (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P s = P t) ∧
        filtrationExpectation P = 0) ∧
      (Antitone R ∧ (∃ t, R t = ⊥) ∧ (∃ t, R t = ⊤) ∧
        (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → R s = R t) ∧
        filtrationExpectation R = 0) ∧
      filtrationPairing P P + filtrationPairing R R = 1 ∧
      filtrationExpectation (fun t ↦ (tensorFiltration P R t).map q) < 0 ∧
      ∀ (A : ℝ → Submodule K E) (B : ℝ → Submodule K F),
        (Antitone A ∧ (∃ t, A t = ⊥) ∧ (∃ t, A t = ⊤) ∧
          (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → A s = A t) ∧
          filtrationExpectation A = 0) →
        (Antitone B ∧ (∃ t, B t = ⊥) ∧ (∃ t, B t = ⊤) ∧
          (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → B s = B t) ∧
          filtrationExpectation B = 0) →
        0 < filtrationPairing A A + filtrationPairing B B →
        filtrationExpectation (fun t ↦ (tensorFiltration P R t).map q) ≤
          filtrationExpectation (fun t ↦ (tensorFiltration A B t).map q) /
            Real.sqrt (filtrationPairing A A + filtrationPairing B B) := by
  obtain ⟨P₀, R₀, hP₀, hR₀, _, hneg₀⟩ :=
    exists_centered_negative_tensor_filtrations_of_not_geometricallySemistable q hq hQ hns
  exact exists_normalized_tensor_quotient_optimizer q hq finrank_pos finrank_pos
    P₀ R₀ hP₀ hR₀ hneg₀

end Submodule

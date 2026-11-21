/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Optimal.Basic
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Optimal.Instability

/-!
# Global optimizers from binary geometric instability

Geometric nonsemistability of a surjective positive-rank tensor quotient produces
a unit negative global optimizer over the original characteristic-zero field.
The comparison ranges over all admissible centered finite real filtration pairs.
Expectations and self-pairings retain reciprocal-rank normalization.

This is the binary existence implication of [ChenMoriwaki2020], Theorem 5.4.3.
It is weaker than the full finite-family statement and does not include the
general variational inequality (5.13).
-/

@[expose] public section

open Module ArakelovGeometry ArakelovGeometry.InvariantTheory
open scoped TensorProduct

namespace Submodule

universe u

variable {K : Type u} {E F Q : Type*} [Field K] [CharZero K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Nontrivial E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F] [Nontrivial F]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Nontrivial Q]

/-- Geometric nonsemistability of the tensor quotient yields a unit negative
global optimizer. This is the binary existence implication of
[ChenMoriwaki2020], Theorem 5.4.3, without the full variational inequality (5.13).
The comparison ranges over all admissible centered finite real filtration pairs
over the original characteristic-zero field. -/
theorem exists_normalized_tensor_quotient_optimizer_of_not_geometricallySemistable
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q) (hQ : 0 < finrank K Q)
    (hns : ¬ IsGeometricallySemistableTensorQuotient (LiftedBoolTensorFactors E F)
      (q.comp (boolTensorPairEquiv K E F).toLinearMap)) :
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

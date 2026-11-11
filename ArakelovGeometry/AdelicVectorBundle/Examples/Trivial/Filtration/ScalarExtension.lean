/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.QuotientDegree
public import ArakelovGeometry.AdelicVectorBundle.Tensor.BaseChange
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Descent.InfiniteGalois

/-!
# Scalar extension of actual finite real filtrations

Actual subspace layers and their quotient images commute with scalar extension.
The intrinsic expectation and pairing retain the real weights and reciprocal-rank
normalizations. These are the scalar-extension inputs for the binary conditional
rationality statement used on page 31 of `bost.pdf`; they do not assert that
geometric instability supplies a negative candidate. No finite degree of the
extension field is required. Existing trivial-norm APIs identify these actual
filtrations with the corresponding completed trivial-place norms.
-/

@[expose] public section

open Module ArakelovGeometry
open scoped TensorProduct

namespace Submodule

variable {K L E Q : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup E] [Module K E] [AddCommGroup Q] [Module K Q]

/-- Actual subspace images commute with scalar extension, for every linear map. -/
theorem baseChange_map_eq (U : Submodule K E) (q : E →ₗ[K] Q) :
    (U.map q).baseChange L = (U.baseChange L).map (q.baseChange L) := by
  rw [baseChange_eq_span, baseChange_eq_span, map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

/-- The extended basis describes the actual extended weighted layer. -/
theorem baseChange_span_basis_weights {ι : Type*} (b : Basis ι K E)
    (w : ι → ℝ) (t : ℝ) :
    (span K (b '' {i | t ≤ w i})).baseChange L =
      span L (b.baseChange L '' {i | t ≤ w i}) := by
  rw [baseChange_span, Set.image_image]
  congr 2
  funext i
  exact (Basis.baseChange_apply L b i).symm

/-- The four genuine finite-filtration conditions are preserved by scalar extension. -/
theorem finite_filtration_baseChange (F : ℝ → Submodule K E)
    (hF : Antitone F) (hb : ∃ t, F t = ⊥) (ht : ∃ t, F t = ⊤)
    (hl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    Antitone (fun t ↦ (F t).baseChange L) ∧
      (∃ t, (F t).baseChange L = ⊥) ∧ (∃ t, (F t).baseChange L = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t →
        (F s).baseChange L = (F t).baseChange L) := by
  obtain ⟨b, hb⟩ := hb
  obtain ⟨u, ht⟩ := ht
  refine ⟨fun _ _ h ↦ baseChange_mono L (hF h),
    ⟨b, by rw [hb, baseChange_bot]⟩, ⟨u, by rw [ht, baseChange_top]⟩, ?_⟩
  intro t
  obtain ⟨ε, hε, he⟩ := hl t
  exact ⟨ε, hε, fun s hs hst ↦ congrArg (baseChange L) (he s hs hst)⟩

variable [FiniteDimensional K E]

/-- Actual finite real-filtration expectation is unchanged by arbitrary field extension. -/
theorem filtrationExpectation_baseChange (F : ℝ → Submodule K E)
    (hF : Antitone F) (hb : ∃ t, F t = ⊥) (ht : ∃ t, F t = ⊤)
    (hl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    filtrationExpectation (fun t ↦ (F t).baseChange L) = filtrationExpectation F := by
  obtain ⟨b, w, _, hw, _⟩ := exists_common_weighted_basis hF hb ht hl hF hb ht hl
  have hwL t : (F t).baseChange L = span L (b.baseChange L '' {i | t ≤ w i}) := by
    rw [hw, baseChange_span_basis_weights]
  rw [filtrationExpectation_eq_sum_weights (b.baseChange L) w hwL,
    filtrationExpectation_eq_sum_weights b w hw, Module.finrank_baseChange]

/-- Actual pairings retain the common real weights and the reciprocal-rank factor. -/
theorem filtrationPairing_baseChange (F G : ℝ → Submodule K E)
    (hF : Antitone F) (hFb : ∃ t, F t = ⊥) (hFt : ∃ t, F t = ⊤)
    (hFl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hG : Antitone G) (hGb : ∃ t, G t = ⊥) (hGt : ∃ t, G t = ⊤)
    (hGl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → G s = G t) :
    filtrationPairing (fun t ↦ (F t).baseChange L) (fun t ↦ (G t).baseChange L) =
      filtrationPairing F G := by
  obtain ⟨b, w, v, hw, hv, _⟩ := exists_common_weighted_basis hF hFb hFt hFl hG hGb hGt hGl
  have hwL t : (F t).baseChange L = span L (b.baseChange L '' {i | t ≤ w i}) := by
    rw [hw, baseChange_span_basis_weights]
  have hvL t : (G t).baseChange L = span L (b.baseChange L '' {i | t ≤ v i}) := by
    rw [hv, baseChange_span_basis_weights]
  rw [filtrationPairing_eq_sum_weights (b.baseChange L) w v hwL hvL,
    filtrationPairing_eq_sum_weights b w v hw hv, Module.finrank_baseChange]

/-- The actual quotient expectation is preserved by extending its adapted image basis.
This compares the same quotient layers, without comparing determinant-support index types. -/
theorem filtrationExpectation_image_baseChange [FiniteDimensional K Q]
    (F : ℝ → Submodule K E)
    (hF : Antitone F) (hb : ∃ t, F t = ⊥) (ht : ∃ t, F t = ⊤)
    (hl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (q : E →ₗ[K] Q) (hq : Function.Surjective q) :
    filtrationExpectation (fun t ↦ ((F t).baseChange L).map (q.baseChange L)) =
      filtrationExpectation (fun t ↦ (F t).map q) := by
  obtain ⟨b, w, _, hw, _⟩ := exists_common_weighted_basis hF hb ht hl hF hb ht hl
  obtain ⟨c, d, hd⟩ := exists_weighted_basis_image b w q hq
  have hqF t : (F t).map q = span K (c '' {i | t ≤ d i}) := by rw [hw]; exact hd t
  have hqL t : ((F t).baseChange L).map (q.baseChange L) =
      span L (c.baseChange L '' {i | t ≤ d i}) := by
    rw [← baseChange_map_eq, hqF, baseChange_span_basis_weights]
  rw [filtrationExpectation_eq_sum_weights (c.baseChange L) d hqL,
    filtrationExpectation_eq_sum_weights c d hqF, Module.finrank_baseChange]

end Submodule

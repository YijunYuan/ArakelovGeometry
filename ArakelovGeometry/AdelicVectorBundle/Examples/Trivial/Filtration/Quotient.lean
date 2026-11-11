/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.Quotient

/-!
# Quotient filtrations at the trivial place

The actual quotient norm has precisely the images of the original closed
balls as its filtration levels. Applied to a prescribed real filtration,
this preserves each original threshold, including endpoints and zero spaces.
-/

@[expose] public section

namespace ArakelovGeometry.NormFamily

noncomputable section

open AdelicStructure

universe u v w

variable {K : Type u} [Field K] {E : Type v} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {Q : Type w} [AddCommGroup Q] [Module K Q]

open Classical in
/-- The literal ball filtration of the actual quotient norm is the image
of the original ball filtration, at the same included threshold. -/
theorem trivialFiltration_pushforward
    (ξ : NormFamily (singleTrivialPlace K) E) (hξ : ξ.IsUltrametric)
    (q : E →ₗ[K] Q) (hq : Function.Surjective q) (t : ℝ) :
    (ξ.pushforward q hq).trivialFiltration (hξ.pushforward q hq) t =
      (ξ.trivialFiltration hξ t).map q := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hn⟩ := ξ.exists_trivialSeminorm_pushforward_lift q hq hξ y
    exact Submodule.mem_map.mpr ⟨x, hn ▸ hy, hx⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact (ξ.trivialSeminorm_pushforward_le q hq x).trans hx

open Classical in
/-- The norm realization of an arbitrary prescribed real filtration has
exactly its threshold-wise image as the actual quotient norm filtration. -/
theorem trivialFiltration_pushforward_ofTrivialFiltration
    (F : ℝ → Submodule K E) (hF : Antitone F)
    (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (q : E →ₗ[K] Q) (hq : Function.Surjective q) (t : ℝ) :
    ((ofTrivialFiltration F hF hbot htop hleft).pushforward q hq).trivialFiltration
      ((ofTrivialFiltration_isUltrametric F hF hbot htop hleft).pushforward q hq) t =
      (F t).map q := by
  rw [trivialFiltration_pushforward, trivialFiltration_ofTrivialFiltration]

end

end ArakelovGeometry.NormFamily

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.SlopesFinite
public import ArakelovGeometry.AdelicVectorBundle.SlopesLinearMap

/-!
# The surjective slope inequality, including infinite height

Actual extremal-slope finiteness supplies the remaining infinite-height case
of source Proposition 4.3.31(2). The zero surjection is stated separately:
its target minimum is `⊤`, without adding the height of the zero map.
-/

@[expose] public section

namespace ArakelovGeometry

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace AdelicVectorBundle

variable [S.IsProper]

/-- Source Proposition 4.3.31(2) for a nonzero actual surjection. Infinite
height is allowed: the target minimum is strictly above `⊥` by the proved
finiteness theorem, so its sum with `⊤` is `⊤`. -/
theorem minimalSlope_le_minimalSlope_add_mapHeight_of_surjective
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (f : E →ₗ[K] F) (hs : Function.Surjective f) (hf : f ≠ 0) :
    V.minimalSlope hS hN ≤ W.minimalSlope hS hN + V.mapHeight W f := by
  by_cases ht : V.mapHeight W f = ⊤
  · have hr : 0 < Module.finrank K f.range := Nat.pos_of_ne_zero (fun hz ↦
      hf (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
    have hF : 0 < Module.finrank K F := hr.trans_le f.range.finrank_le
    rw [ht, EReal.add_top_of_ne_bot (W.bot_lt_minimalSlope hS hN hF).ne']
    exact le_top
  · exact V.minimalSlope_le_minimalSlope_add_mapHeight_of_surjective_of_ne_top
      W hS hN f hs hf ht

/-- The zero-map surjective case of source Proposition 4.3.31(2): the
target has rank zero and minimal slope `⊤`. No extended-real sum involving
the height of the zero map is needed for its automatic bound. -/
theorem minimalSlope_target_eq_top_of_zero_surjective
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (f : E →ₗ[K] F) (hs : Function.Surjective f) (hf : f = 0) :
    W.minimalSlope hS hN = ⊤ ∧ V.minimalSlope hS hN ≤ W.minimalSlope hS hN := by
  let : Subsingleton F := ⟨fun y z ↦ by
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨x', rfl⟩ := hs z
    simp only [hf, LinearMap.zero_apply]⟩
  have hW := W.minimalSlope_eq_top_of_finrank_eq_zero hS hN
    Module.finrank_zero_of_subsingleton
  exact ⟨hW, hW ▸ le_top⟩

end AdelicVectorBundle

end ArakelovGeometry

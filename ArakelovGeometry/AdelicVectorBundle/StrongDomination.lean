/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Domination

/-!
# Strong domination of norm families

We use the first criterion in Chen–Moriwaki, Corollary 4.1.10:
domination of the family and of its distance to its actual completed bidual.
The equivalent basis criteria are separate results. Completed bidual isometries
give the ultrametric and rank-one cases; triple duality makes the dual of any
dominated family strongly dominated without a normalization assumption.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Strong domination, using the bidual-distance criterion from the source.
The bidual is pulled back by canonical evaluation on the original space. -/
def IsStronglyDominated (ξ : NormFamily S E) : Prop :=
  ξ.IsDominated ∧ HasIntegrableBounds
    (ξ.localDist (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K))) S.v

theorem IsStronglyDominated.isDominated {ξ : NormFamily S E}
    (hξ : ξ.IsStronglyDominated) : ξ.IsDominated := hξ.1

/-- Actual isometry with the completed bidual makes the extra distance zero. -/
theorem IsDominated.strong_of_bidual_eq {ξ : NormFamily S E} (hξ : ξ.IsDominated)
    (he : ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K) = ξ) : ξ.IsStronglyDominated := by
  refine ⟨hξ, ?_⟩
  rw [he]
  have hz : ξ.localDist ξ = 0 := funext fun ω ↦ ξ.localDist_self ω
  rw [hz]
  exact integrable_hasIntegrableBounds (integrable_zero S.Ω ℝ S.v)

/-- The dual of every dominated family is strongly dominated.
This consumes exact completed triple duality, including trivially valued fibres. -/
theorem IsDominated.strong_dual {ξ : NormFamily S E} (hξ : ξ.IsDominated) :
    ξ.dual.IsStronglyDominated :=
  hξ.dual.strong_of_bidual_eq ξ.dual_dual_dual_pullback

/-- Under the source's usual Archimedean normalization, an ultrametric family
is strongly dominated exactly when it is dominated. -/
theorem isStronglyDominated_iff_isDominated_of_ultrametric (ξ : NormFamily S E)
    (hξ : ξ.IsUltrametric)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ξ.IsStronglyDominated ↔ ξ.IsDominated :=
  ⟨fun h ↦ h.1, fun h ↦ h.strong_of_bidual_eq (ξ.dual_dual_pullback_eq hξ hS)⟩

/-- In dimensions zero and one, no Archimedean normalization is needed. -/
theorem isStronglyDominated_iff_isDominated_of_finrank_le_one (ξ : NormFamily S E)
    (hr : Module.finrank K E ≤ 1) : ξ.IsStronglyDominated ↔ ξ.IsDominated :=
  ⟨fun h ↦ h.1,
    fun h ↦ h.strong_of_bidual_eq (ξ.dual_dual_pullback_eq_of_finrank_le_one hr)⟩

/-- The zero-dimensional family is strongly dominated. -/
theorem isStronglyDominated_of_subsingleton [Subsingleton E] (ξ : NormFamily S E) :
    ξ.IsStronglyDominated :=
  (ξ.isStronglyDominated_iff_isDominated_of_finrank_le_one
    (by rw [Module.finrank_zero_of_subsingleton]; omega)).2
    ξ.isDominated_of_subsingleton

/-- Taking completed biduals and pulling back by evaluation contracts local distance. -/
theorem localDist_bidual_pullback_le (ξ η : NormFamily S E) (ω : S.Ω) :
    (ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)).localDist
      (η.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)) ω ≤
      ξ.localDist η ω :=
  (ξ.dual.dual.localDist_pullback_le η.dual.dual
    (Module.Dual.eval K E) (Module.eval_apply_injective K) ω).trans
      ((ξ.dual.localDist_dual_le η.dual ω).trans (ξ.localDist_dual_le η ω))

/-- Strong domination transfers across a distance with an integrable upper envelope. -/
theorem IsStronglyDominated.of_localDist {ξ η : NormFamily S E}
    (hξ : ξ.IsStronglyDominated) (hd : HasIntegrableUpperBound (ξ.localDist η) S.v) :
    η.IsStronglyDominated := by
  refine ⟨hξ.1.of_localDist hd, ?_, ?_⟩
  · apply ((hd.add hξ.2.1).add hd).mono
    apply Filter.Eventually.of_forall
    intro ω
    let ξbb := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
    let ηbb := η.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
    have h₁ := η.localDist_triangle ξ ηbb ω
    have h₂ := ξ.localDist_triangle ξbb ηbb ω
    have h₃ := ξ.localDist_bidual_pullback_le η ω
    rw [η.localDist_comm ξ ω] at h₁
    change η.localDist ηbb ω ≤ ξ.localDist η ω + ξ.localDist ξbb ω + ξ.localDist η ω
    change ξbb.localDist ηbb ω ≤ ξ.localDist η ω at h₃
    linarith
  · exact ⟨0, integrable_zero S.Ω ℝ S.v,
      Filter.Eventually.of_forall fun ω ↦ η.localDist_nonneg _ ω⟩

end ArakelovGeometry.NormFamily

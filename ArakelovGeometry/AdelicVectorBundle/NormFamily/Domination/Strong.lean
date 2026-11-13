/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Basic

import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Strong domination of norm families

The bidual-distance criterion of Chen–Moriwaki, Corollary 4.1.10, combines domination
with integrable envelopes for the local distance to the completed bidual, pulled
back along the evaluation map. This distance is nonnegative, so its lower envelope
can be chosen to be zero; the upper-bound characterization records this equivalence.
Measurability remains a separate property.

Completed bidual isometries give the ultrametric and rank-one cases. Triple duality
shows that the dual of a dominated family is strongly dominated without an
Archimedean normalization assumption. Basis-distance criteria are developed in
the corresponding domination modules.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Strong domination, using the bidual-distance criterion from the source.
The bidual is pulled back by canonical evaluation on the original space. -/
class IsStronglyDominated (ξ : NormFamily S E) : Prop where
  /-- Domination of the norm family. -/
  dominated : ξ.IsDominated
  /-- Integrable bounds on the distance to the completed bidual. -/
  bidual_bounds : HasIntegrableBounds
    (ξ.localDist (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K))) S.v

attribute [instance] IsStronglyDominated.dominated

/-- The two components of strong domination. -/
theorem isStronglyDominated_iff (ξ : NormFamily S E) :
    ξ.IsStronglyDominated ↔ ξ.IsDominated ∧ HasIntegrableBounds
      (ξ.localDist (ξ.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K))) S.v :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- The bidual distance is nonnegative, so its lower integrable envelope is automatic.
Strong domination therefore only requires an upper envelope in addition to domination. -/
theorem isStronglyDominated_iff_hasIntegrableUpperBound (ξ : NormFamily S E) :
    ξ.IsStronglyDominated ↔ ξ.IsDominated ∧ HasIntegrableUpperBound
      (ξ.localDist (ξ.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K))) S.v := by
  rw [isStronglyDominated_iff]
  refine and_congr_right fun _ ↦ ?_
  exact ⟨And.left, fun h ↦ ⟨h, 0, integrable_zero S.Ω ℝ S.v,
    Filter.Eventually.of_forall fun ω ↦ ξ.localDist_nonneg _ ω⟩⟩

/-- Strong domination is invariant under equivalence pullback, without normalization. -/
theorem IsStronglyDominated.pullbackEquiv {ξ : NormFamily S E}
    (hξ : ξ.IsStronglyDominated) {F : Type*} [AddCommGroup F] [Module K F]
    [FiniteDimensional K F] (e : F ≃ₗ[K] E) :
    (ξ.pullback e.toLinearMap e.injective).IsStronglyDominated := by
  apply (isStronglyDominated_iff_hasIntegrableUpperBound _).mpr
  refine ⟨hξ.1.pullback e.toLinearMap e.injective, ?_⟩
  rw [ξ.pullbackEquiv_bidual e]
  exact hξ.2.1.mono (Filter.Eventually.of_forall fun ω ↦
    ξ.localDist_pullback_le _ e.toLinearMap e.injective ω)

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
    [hξ : ξ.IsUltrametric]
    [hS : S.IsArchimedeanNormalized] :
    ξ.IsStronglyDominated ↔ ξ.IsDominated :=
  ⟨fun h ↦ h.1, fun h ↦ h.strong_of_bidual_eq (ξ.dual_dual_pullback_eq)⟩

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
  apply (η.isStronglyDominated_iff_hasIntegrableUpperBound).2
  refine ⟨hξ.1.of_localDist hd, ?_⟩
  apply ((hd.add hξ.2.1).add hd).mono
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

instance instIsStronglyDominatedDual (ξ : NormFamily S E) [ξ.IsDominated] :
    ξ.dual.IsStronglyDominated :=
  IsDominated.strong_dual inferInstance

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NormFamily
attribute [instance] isStronglyDominated_of_subsingleton
end ArakelovGeometry.NormFamily

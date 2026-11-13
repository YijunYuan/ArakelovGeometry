/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basic

import ArakelovGeometry.Analysis.NormedSpace.FiniteDimensional
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Quotients of norm families

Scalar extension of a surjective linear map and the canonical completed-fibre
quotient identification. Quotient norms use Mathlib's norm on the quotient by
the completed kernel, transported to the actual target fibre.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
variable {E : Type w} [AddCommGroup E] [Module K E]
variable {G : Type w'} [AddCommGroup G] [Module K G]

/-- Scalar extension preserves the kernel as the image of the extended kernel inclusion. -/
theorem baseChange_ker (π : E →ₗ[K] G) (ω : S.Ω) :
    (π.baseChange (S.ϕ ω).Completion).ker =
      (π.ker.subtype.baseChange (S.ϕ ω).Completion).range := by
  exact LinearMap.exact_iff.mp
    (Module.Flat.lTensor_exact (S.ϕ ω).Completion π.exact_subtype_ker_map)

/-- The quotient by the image of the completed kernel is canonically the target fibre. -/
noncomputable def completedQuotientEquiv (π : E →ₗ[K] G)
    (hπ : Function.Surjective π) (ω : S.Ω) :
    (((S.ϕ ω).Completion ⊗[K] E) ⧸
        (π.ker.subtype.baseChange (S.ϕ ω).Completion).range) ≃ₗ[(S.ϕ ω).Completion]
      (S.ϕ ω).Completion ⊗[K] G :=
  (Submodule.quotEquivOfEq _ _ (baseChange_ker π ω).symm).trans
    ((π.baseChange (S.ϕ ω).Completion).quotKerEquivOfSurjective
      (LinearMap.baseChange_surjective _ hπ))

@[simp]
theorem completedQuotientEquiv_mk (π : E →ₗ[K] G)
    (hπ : Function.Surjective π) (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    completedQuotientEquiv π hπ ω (Submodule.Quotient.mk x) =
      π.baseChange (S.ϕ ω).Completion x := by
  simp [completedQuotientEquiv]

variable (ξ : NormFamily S E)

/-- The canonical quotient seminorm transported onto the actual target fibre. -/
noncomputable def quotientSeminorm (π : E →ₗ[K] G)
    (hπ : Function.Surjective π) (ω : S.Ω) :
    Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] G) := by
  letI := ξ.fibreNormedAddCommGroup ω
  letI := ξ.fibreNormedSpace ω
  exact (normSeminorm (S.ϕ ω).Completion
    (((S.ϕ ω).Completion ⊗[K] E) ⧸ (π.baseChange (S.ϕ ω).Completion).ker)).comp
      ((π.baseChange (S.ϕ ω).Completion).quotKerEquivOfSurjective
        (LinearMap.baseChange_surjective _ hπ)).symm.toLinearMap

/-- The quotient map is a contraction for the canonical quotient seminorm. -/
theorem quotientSeminorm_le (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.quotientSeminorm π hπ ω (π.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  change ‖((π.baseChange (S.ϕ ω).Completion).quotKerEquivOfSurjective
    (LinearMap.baseChange_surjective _ hπ)).symm
      (π.baseChange (S.ϕ ω).Completion x)‖ ≤ ‖x‖
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  exact Submodule.Quotient.norm_mk_le _ x

/-- Every target vector has lifts with norm arbitrarily close to the quotient seminorm. -/
theorem exists_quotientSeminorm_lift_lt (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] G) {ε : ℝ} (hε : 0 < ε) :
    ∃ x, π.baseChange (S.ϕ ω).Completion x = z ∧
      ξ.norm ω x < ξ.quotientSeminorm π hπ ω z + ε := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let e := (π.baseChange (S.ϕ ω).Completion).quotKerEquivOfSurjective
    (LinearMap.baseChange_surjective _ hπ)
  obtain ⟨x, hx, hn⟩ := Submodule.Quotient.norm_mk_lt (e.symm z) hε
  refine ⟨x, ?_, hn⟩
  have := congrArg e hx
  simpa [e] using this

/-- A lower bound for the quotient is exactly a common lower bound for all its lifts. -/
theorem le_quotientSeminorm_iff (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] G) (a : ℝ) :
    a ≤ ξ.quotientSeminorm π hπ ω z ↔
      ∀ x, π.baseChange (S.ϕ ω).Completion x = z → a ≤ ξ.norm ω x := by
  constructor
  · intro h x hx
    rw [← hx] at h
    exact h.trans (ξ.quotientSeminorm_le π hπ ω x)
  · intro h
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨x, hx, hn⟩ := ξ.exists_quotientSeminorm_lift_lt π hπ ω z hε
    exact (h x hx).trans hn.le

/-- The quotient norm is the infimum over actual completed-fibre lifts. -/
theorem quotientSeminorm_eq_sInf (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] G) :
    ξ.quotientSeminorm π hπ ω z =
      sInf (ξ.norm ω '' {x | π.baseChange (S.ϕ ω).Completion x = z}) := by
  have hne : (ξ.norm ω '' {x | π.baseChange (S.ϕ ω).Completion x = z}).Nonempty := by
    obtain ⟨x, hx⟩ := LinearMap.baseChange_surjective (S.ϕ ω).Completion hπ z
    exact ⟨_, ⟨x, hx, rfl⟩⟩
  have hb : BddBelow (ξ.norm ω '' {x | π.baseChange (S.ϕ ω).Completion x = z}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    exact ξ.norm_nonneg ω x
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨x, hx, rfl⟩
    rw [← hx]
    exact ξ.quotientSeminorm_le π hπ ω x
  · apply (ξ.le_quotientSeminorm_iff π hπ ω z _).2
    intro x hx
    exact csInf_le hb ⟨x, hx, rfl⟩

/-- Positive rescaling commutes with the canonical quotient seminorm. -/
theorem quotientSeminorm_scale (a : S.Ω → ℝ) (ha : ∀ ω, 0 < a ω)
    (π : E →ₗ[K] G) (hπ : Function.Surjective π) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] G) :
    (ξ.scale a ha).quotientSeminorm π hπ ω z = a ω * ξ.quotientSeminorm π hπ ω z := by
  apply le_antisymm
  · have h : (ξ.scale a ha).quotientSeminorm π hπ ω z / a ω ≤
        ξ.quotientSeminorm π hπ ω z := by
      apply (ξ.le_quotientSeminorm_iff π hπ ω z _).2
      intro x hx
      apply (div_le_iff₀ (ha ω)).2
      rw [← hx, mul_comm]
      exact (ξ.scale a ha).quotientSeminorm_le π hπ ω x
    simpa only [mul_comm] using (div_le_iff₀ (ha ω)).1 h
  · apply ((ξ.scale a ha).le_quotientSeminorm_iff π hπ ω z _).2
    intro x hx
    rw [scale_norm, ← hx]
    exact mul_le_mul_of_nonneg_left (ξ.quotientSeminorm_le π hπ ω x) (ha ω).le

/-- A bijective quotient map preserves every norm value. -/
theorem quotientSeminorm_of_injective (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (hi : Function.Injective π) (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.quotientSeminorm π hπ ω (π.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x := by
  apply le_antisymm (ξ.quotientSeminorm_le π hπ ω x)
  apply (ξ.le_quotientSeminorm_iff π hπ ω _ _).2
  intro y hy
  have hxy : y = x := Module.Flat.lTensor_preserves_injective_linearMap π hi hy
  rw [hxy]

/-- Quotienting along the identity recovers the original seminorm. -/
@[simp]
theorem quotientSeminorm_id (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.quotientSeminorm LinearMap.id Function.surjective_id ω x = ξ.norm ω x := by
  simpa using ξ.quotientSeminorm_of_injective LinearMap.id Function.surjective_id
    Function.injective_id ω x

/-- The quotient seminorm retains the non-Archimedean triangle inequality. -/
theorem quotientSeminorm_add_le_max [hξ : ξ.IsUltrametricAtFinitePlaces]
    (π : E →ₗ[K] G) (hπ : Function.Surjective π) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z t : (S.ϕ ω).Completion ⊗[K] G) :
    ξ.quotientSeminorm π hπ ω (z + t) ≤
      max (ξ.quotientSeminorm π hπ ω z) (ξ.quotientSeminorm π hπ ω t) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, hn⟩ := ξ.exists_quotientSeminorm_lift_lt π hπ ω z hε
  obtain ⟨y, hy, hm⟩ := ξ.exists_quotientSeminorm_lift_lt π hπ ω t hε
  calc
    ξ.quotientSeminorm π hπ ω (z + t) =
        ξ.quotientSeminorm π hπ ω (π.baseChange (S.ϕ ω).Completion (x + y)) := by
          rw [(π.baseChange (S.ϕ ω).Completion).map_add, hx, hy]
    _ ≤ ξ.norm ω (x + y) := ξ.quotientSeminorm_le π hπ ω (x + y)
    _ ≤ max (ξ.norm ω x) (ξ.norm ω y) := hξ ω hω x y
    _ ≤ max (ξ.quotientSeminorm π hπ ω z + ε)
        (ξ.quotientSeminorm π hπ ω t + ε) := max_le_max hn.le hm.le
    _ = max (ξ.quotientSeminorm π hπ ω z) (ξ.quotientSeminorm π hπ ω t) + ε :=
      max_add_add_right _ _ _

/-- The canonical completed quotient identification transports exactly Mathlib's
quotient norm, not just a comparable norm. -/
theorem completedQuotientEquiv_norm (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (ω : S.Ω) :
    letI := ξ.fibreNormedAddCommGroup ω
    ∀ z : ((S.ϕ ω).Completion ⊗[K] E) ⧸
        (π.ker.subtype.baseChange (S.ϕ ω).Completion).range,
      ξ.quotientSeminorm π hπ ω (completedQuotientEquiv π hπ ω z) = ‖z‖ := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  intro z
  let e := (π.baseChange (S.ϕ ω).Completion).quotKerEquivOfSurjective
    (LinearMap.baseChange_surjective _ hπ)
  change ‖e.symm (e ((Submodule.quotEquivOfEq _ _ (baseChange_ker π ω).symm) z))‖ = ‖z‖
  rw [LinearEquiv.symm_apply_apply]
  exact (Submodule.quotLIEOfEq _ _ (baseChange_ker π ω).symm).norm_map z

variable [FiniteDimensional K E]

/-- Finite-dimensional closedness makes the quotient seminorm separated, including
at trivially valued places and for non-ultrametric ambient norms. -/
theorem quotientSeminorm_eq_zero_iff (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] G) :
    ξ.quotientSeminorm π hπ ω z = 0 ↔ z = 0 := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let : IsClosed ((π.baseChange (S.ϕ ω).Completion).ker :
      Set ((S.ϕ ω).Completion ⊗[K] E)) :=
    finiteDimensional_submodule_isClosed _
  change ‖((π.baseChange (S.ϕ ω).Completion).quotKerEquivOfSurjective
    (LinearMap.baseChange_surjective _ hπ)).symm z‖ = 0 ↔ z = 0
  rw [norm_eq_zero, LinearEquiv.map_eq_zero_iff]

/-- The quotient norm family along a surjective map, on its actual completed target fibres. -/
noncomputable def pushforward (π : E →ₗ[K] G) (hπ : Function.Surjective π) :
    NormFamily S G where
  norm ω := ξ.quotientSeminorm π hπ ω
  norm_eq_zero_iff := ξ.quotientSeminorm_eq_zero_iff π hπ

@[simp]
theorem pushforward_norm (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] G) :
    (ξ.pushforward π hπ).norm ω z = ξ.quotientSeminorm π hπ ω z := rfl

/-- The quotient family evaluates as the infimum over all completed-fibre lifts. -/
theorem pushforward_norm_eq_sInf (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] G) :
    (ξ.pushforward π hπ).norm ω z =
      sInf (ξ.norm ω '' {x | π.baseChange (S.ϕ ω).Completion x = z}) :=
  ξ.quotientSeminorm_eq_sInf π hπ ω z

/-- The actual quotient norm contracts the scalar-extended quotient map. -/
theorem pushforward_norm_le (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.pushforward π hπ).norm ω (π.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x :=
  ξ.quotientSeminorm_le π hπ ω x

/-- Infima of lift norms need not be attained; arbitrarily close lifts always exist. -/
theorem exists_pushforward_lift_lt (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] G) {ε : ℝ} (hε : 0 < ε) :
    ∃ x, π.baseChange (S.ϕ ω).Completion x = z ∧
      ξ.norm ω x < (ξ.pushforward π hπ).norm ω z + ε :=
  ξ.exists_quotientSeminorm_lift_lt π hπ ω z hε

/-- Positive rescaling and the quotient operation commute. -/
theorem scale_pushforward (a : S.Ω → ℝ) (ha : ∀ ω, 0 < a ω)
    (π : E →ₗ[K] G) (hπ : Function.Surjective π) :
    (ξ.scale a ha).pushforward π hπ = (ξ.pushforward π hπ).scale a ha := by
  ext ω z
  exact ξ.quotientSeminorm_scale a ha π hπ ω z

/-- Quotienting along an isomorphism preserves the norm of every image. -/
theorem pushforward_norm_of_injective (π : E →ₗ[K] G) (hπ : Function.Surjective π)
    (hi : Function.Injective π) (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.pushforward π hπ).norm ω (π.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x :=
  ξ.quotientSeminorm_of_injective π hπ hi ω x

@[simp]
theorem pushforward_id : ξ.pushforward LinearMap.id Function.surjective_id = ξ := by
  ext ω x
  exact ξ.quotientSeminorm_id ω x

/-- Surjectivity from a zero source forces every quotient-fibre norm to vanish. -/
theorem pushforward_norm_of_subsingleton [Subsingleton E]
    (π : E →ₗ[K] G) (hπ : Function.Surjective π) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] G) : (ξ.pushforward π hπ).norm ω z = 0 := by
  obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective (S.ϕ ω).Completion hπ z
  apply le_antisymm
  · calc
      (ξ.pushforward π hπ).norm ω (π.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x :=
        ξ.pushforward_norm_le π hπ ω x
      _ = 0 := ξ.norm_eq_zero_of_subsingleton ω x
  · exact (ξ.pushforward π hπ).norm_nonneg ω _

/-- Quotient families remain ultrametric at every non-Archimedean place. -/
theorem IsUltrametricAtFinitePlaces.pushforward
    {ξ : NormFamily S E} (hξ : ξ.IsUltrametricAtFinitePlaces)
    (π : E →ₗ[K] G)
      (hπ : Function.Surjective π) : (ξ.pushforward π hπ).IsUltrametricAtFinitePlaces :=
  ⟨fun ω hω x y ↦ ξ.quotientSeminorm_add_le_max π hπ ω hω x y⟩

/-- Quotient by a subspace, using the scalar extension of its canonical quotient map. -/
noncomputable def quotient (F : Submodule K E) : NormFamily S (E ⧸ F) :=
  ξ.pushforward F.mkQ F.mkQ_surjective

/-- The canonical map to a subspace quotient is a contraction on every completed fibre. -/
theorem quotient_norm_mk_le (F : Submodule K E) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.quotient F).norm ω (F.mkQ.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x :=
  ξ.pushforward_norm_le F.mkQ F.mkQ_surjective ω x

/-- Rescaling commutes with quotient by a subspace. -/
theorem scale_quotient (a : S.Ω → ℝ) (ha : ∀ ω, 0 < a ω) (F : Submodule K E) :
    (ξ.scale a ha).quotient F = (ξ.quotient F).scale a ha :=
  ξ.scale_pushforward a ha F.mkQ F.mkQ_surjective

/-- The quotient by zero recovers the original norm through the canonical map. -/
@[simp]
theorem quotient_bot_norm_mk (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.quotient ⊥).norm ω
      ((⊥ : Submodule K E).mkQ.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x := by
  apply ξ.pushforward_norm_of_injective
  exact LinearMap.ker_eq_bot.mp (Submodule.ker_mkQ ⊥)

/-- The quotient by the whole space has the unique zero norm. -/
@[simp]
theorem quotient_top_norm (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] (E ⧸ (⊤ : Submodule K E))) :
    (ξ.quotient ⊤).norm ω x = 0 :=
  (ξ.quotient ⊤).norm_eq_zero_of_subsingleton ω x

/-- Ultrametricity is preserved by quotienting by any subspace. -/
theorem IsUltrametricAtFinitePlaces.quotient
    {ξ : NormFamily S E} (hξ : ξ.IsUltrametricAtFinitePlaces)
    (F : Submodule K E) : (ξ.quotient F).IsUltrametricAtFinitePlaces :=
  hξ.pushforward F.mkQ F.mkQ_surjective

section Isometry
omit [FiniteDimensional K E]
variable {k : Type*} [Field k] {T : AdelicStructure k}
  {X Y : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
  [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]

/-- A completed isometry descends through any commuting pair of quotient maps. -/
theorem quotientEquiv_norm_eq_of_comp_eq (ξ : NormFamily T X) (η : NormFamily T Y)
    (ω : T.Ω) (e : X ≃ₗ[k] Y) (P : Submodule k X) (Q : Submodule k Y)
    (q : (X ⧸ P) ≃ₗ[k] (Y ⧸ Q))
    (hc : q.toLinearMap.comp P.mkQ = Q.mkQ.comp e.toLinearMap)
    (he : ∀ t, η.norm ω (e.toLinearMap.baseChange (T.ϕ ω).Completion t) = ξ.norm ω t)
    (z : (T.ϕ ω).Completion ⊗[k] (X ⧸ P)) :
    (η.quotient Q).norm ω (q.toLinearMap.baseChange (T.ϕ ω).Completion z) =
      (ξ.quotient P).norm ω z := by
  have hcb : (q.toLinearMap.baseChange (T.ϕ ω).Completion).comp
      (P.mkQ.baseChange (T.ϕ ω).Completion) =
      (Q.mkQ.baseChange (T.ϕ ω).Completion).comp
        (e.toLinearMap.baseChange (T.ϕ ω).Completion) := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hc]
  apply le_antisymm
  · apply (ξ.le_quotientSeminorm_iff P.mkQ P.mkQ_surjective ω z _).2
    intro t ht
    have hl : Q.mkQ.baseChange (T.ϕ ω).Completion
        (e.toLinearMap.baseChange (T.ϕ ω).Completion t) =
        q.toLinearMap.baseChange (T.ϕ ω).Completion z := by
      have h := congrArg (fun f : _ →ₗ[(T.ϕ ω).Completion] _ => f t) hcb
      simpa only [LinearMap.comp_apply, ht] using h.symm
    rw [← hl]
    exact (η.pushforward_norm_le Q.mkQ Q.mkQ_surjective ω _).trans (he t).le
  · apply (η.le_quotientSeminorm_iff Q.mkQ Q.mkQ_surjective ω _ _).2
    intro y hy
    obtain ⟨t, rfl⟩ := LinearMap.baseChange_surjective (T.ϕ ω).Completion e.surjective y
    have hl : P.mkQ.baseChange (T.ϕ ω).Completion t = z := by
      apply Module.Flat.lTensor_preserves_injective_linearMap q.toLinearMap q.injective
      have h := congrArg (fun f : _ →ₗ[(T.ϕ ω).Completion] _ => f t) hcb
      exact h.trans hy
    rw [← hl]
    exact (ξ.pushforward_norm_le P.mkQ P.mkQ_surjective ω t).trans (he t).symm.le

/-- An actual completed isometry induces the canonical quotient-image
isometry. Every completed lift is used; an optimal lift is unnecessary. -/
theorem quotientEquiv_norm_eq (ξ : NormFamily T X) (η : NormFamily T Y)
    (ω : T.Ω) (e : X ≃ₗ[k] Y) (P : Submodule k X)
    (he : ∀ t, η.norm ω (e.toLinearMap.baseChange (T.ϕ ω).Completion t) = ξ.norm ω t)
    (z : (T.ϕ ω).Completion ⊗[k] (X ⧸ P)) :
    let Q := P.map e.toLinearMap
    let q := Submodule.Quotient.equiv P Q e rfl
    (η.quotient Q).norm ω (q.toLinearMap.baseChange (T.ϕ ω).Completion z) =
      (ξ.quotient P).norm ω z := by
  intro Q q
  exact quotientEquiv_norm_eq_of_comp_eq ξ η ω e P Q q (by ext y; rfl) he z

end Isometry

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NormFamily

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E F : Type*} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

variable [FiniteDimensional K E]

instance instIsUltrametricAtFinitePlacesPushforward
    {ξ : NormFamily S E} [hξ : ξ.IsUltrametricAtFinitePlaces]
    (f : E →ₗ[K] F)
      (hf : Function.Surjective f) : (ξ.pushforward f hf).IsUltrametricAtFinitePlaces :=
  hξ.pushforward f hf

instance instIsUltrametricAtFinitePlacesQuotient
    {ξ : NormFamily S E} [hξ : ξ.IsUltrametricAtFinitePlaces]
    (P : Submodule K E) : (ξ.quotient P).IsUltrametricAtFinitePlaces := hξ.quotient P

end ArakelovGeometry.NormFamily

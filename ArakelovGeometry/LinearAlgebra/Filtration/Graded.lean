/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.FiniteFiltration
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Actual graded subquotients of real filtrations

The grade at `t` is the quotient of the actual subspace `F t` by the strict
right-limit subspace inside it. Linear maps preserving thresholds induce maps
on these quotients. No choice of a splitting enters their definition.
-/

@[expose] public section

namespace Submodule

variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]

/-- The strict right limit of a real family of subspaces. -/
noncomputable def filtrationRightLimit (F : ℝ → Submodule K E) (t : ℝ) : Submodule K E :=
  ⨆ s : {s : ℝ // t < s}, F s.val

/-- For a decreasing filtration the strict right limit lies in the current step. -/
theorem filtrationRightLimit_le {F : ℝ → Submodule K E} (hF : Antitone F) (t : ℝ) :
    filtrationRightLimit F t ≤ F t :=
  iSup_le fun s ↦ hF s.property.le

/-- The actual grade, with the strict right limit viewed inside the current subspace. -/
abbrev FiltrationGraded (F : ℝ → Submodule K E) (t : ℝ) :=
  F t ⧸ (filtrationRightLimit F t).comap (F t).subtype

/-- The canonical quotient map from a filtration step to its grade. -/
noncomputable def filtrationGradedMk (F : ℝ → Submodule K E) (t : ℝ) :
    F t →ₗ[K] FiltrationGraded F t :=
  ((filtrationRightLimit F t).comap (F t).subtype).mkQ

@[simp]
theorem filtrationGradedMk_eq_zero (F : ℝ → Submodule K E) (t : ℝ) (x : F t) :
    filtrationGradedMk F t x = 0 ↔ (x : E) ∈ filtrationRightLimit F t :=
  Submodule.Quotient.mk_eq_zero _

/-- A threshold-preserving map preserves the strict right limits. -/
theorem map_filtrationRightLimit_le {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
    (f : E →ₗ[K] V) (hf : ∀ t, F t ≤ (G t).comap f) (t : ℝ) :
    (filtrationRightLimit F t).map f ≤ filtrationRightLimit G t := by
  unfold filtrationRightLimit
  rw [map_iSup]
  exact iSup_le fun s ↦ (map_le_iff_le_comap.mpr (hf s.val)).trans
    (le_iSup (fun s : {s : ℝ // t < s} ↦ G s.val) s)

/-- Restrict a threshold-preserving map to the actual steps. -/
def filtrationStepMap {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
    (f : E →ₗ[K] V) (hf : ∀ t, F t ≤ (G t).comap f) (t : ℝ) : F t →ₗ[K] G t :=
  (f.comp (F t).subtype).codRestrict (G t) (fun x ↦ hf t x.property)

/-- The map on actual graded subquotients induced by a threshold-preserving linear map. -/
noncomputable def filtrationGradedMap {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
    (f : E →ₗ[K] V) (hf : ∀ t, F t ≤ (G t).comap f) (t : ℝ) :
    FiltrationGraded F t →ₗ[K] FiltrationGraded G t :=
  ((filtrationRightLimit F t).comap (F t).subtype).mapQ
    ((filtrationRightLimit G t).comap (G t).subtype) (filtrationStepMap f hf t) (by
      intro x hx
      exact map_filtrationRightLimit_le f hf t ⟨(x : E), hx, rfl⟩)

@[simp]
theorem filtrationGradedMap_mk {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
    (f : E →ₗ[K] V) (hf : ∀ t, F t ≤ (G t).comap f) (t : ℝ) (x : F t) :
    filtrationGradedMap f hf t (filtrationGradedMk F t x) =
      filtrationGradedMk G t (filtrationStepMap f hf t x) := rfl

/-- A map onto the target step induces a surjection onto that target grade. -/
theorem filtrationGradedMap_surjective {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
    (f : E →ₗ[K] V) (hf : ∀ t, F t ≤ (G t).comap f) (t : ℝ)
    (ht : (F t).map f = G t) : Function.Surjective (filtrationGradedMap f hf t) := by
  intro y
  obtain ⟨z, rfl⟩ := ((filtrationRightLimit G t).comap (G t).subtype).mkQ_surjective y
  obtain ⟨x, hx, hxz⟩ := show (z : V) ∈ (F t).map f from ht.symm ▸ z.property
  refine ⟨filtrationGradedMk F t ⟨x, hx⟩, ?_⟩
  change filtrationGradedMk G t (filtrationStepMap f hf t ⟨x, hx⟩) = _
  exact congrArg (filtrationGradedMk G t) (Subtype.ext hxz)

@[simp]
theorem filtrationGradedMap_id (F : ℝ → Submodule K E) (t : ℝ) :
    filtrationGradedMap (LinearMap.id : E →ₗ[K] E) (fun _ ↦ le_rfl) t =
      (LinearMap.id : FiltrationGraded F t →ₗ[K] FiltrationGraded F t) := by
  ext x
  rfl

/-- Induced graded maps commute with composition on the original vector spaces. -/
theorem filtrationGradedMap_comp {W : Type*} [AddCommGroup W] [Module K W]
    {F : ℝ → Submodule K E} {G : ℝ → Submodule K V} {H : ℝ → Submodule K W}
    (f : E →ₗ[K] V) (g : V →ₗ[K] W)
    (hf : ∀ t, F t ≤ (G t).comap f) (hg : ∀ t, G t ≤ (H t).comap g) (t : ℝ) :
    filtrationGradedMap (g.comp f) (fun s _ hx ↦ hg s (hf s hx)) t =
      (filtrationGradedMap g hg t).comp (filtrationGradedMap f hf t) := by
  ext x
  rfl

end Submodule

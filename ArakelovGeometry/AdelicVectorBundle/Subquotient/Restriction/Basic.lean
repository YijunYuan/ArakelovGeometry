/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basic

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Restriction of norm families

An injective linear map remains injective on the completed scalar extensions.
Pulling back a norm along this map therefore gives a norm family. Restriction to
a subspace is the special case of its canonical inclusion, as in
Chen–Moriwaki, §4.1.1.2 (PDF page 222, printed page 206).

Restriction commutes with positive rescaling and preserves ultrametricity.
No finite-dimensionality or regularity hypothesis is needed for these results.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u w w' w''

variable {K : Type u} [Field K] {S : AdelicStructure K}
variable {E : Type w} [AddCommGroup E] [Module K E]
variable {F : Type w'} [AddCommGroup F] [Module K F]
variable {G : Type w''} [AddCommGroup G] [Module K G]

variable (ξ : NormFamily S E)

/-- Pullback of a norm family along an injective linear map, using its scalar
extension at each completed place. -/
noncomputable def pullback (f : F →ₗ[K] E) (hf : Function.Injective f) : NormFamily S F where
  norm ω := (ξ.norm ω).comp (f.baseChange (S.ϕ ω).Completion)
  norm_eq_zero_iff ω x := by
    rw [Seminorm.comp_apply, ξ.norm_eq_zero_iff]
    exact (f.baseChange (S.ϕ ω).Completion).map_eq_zero_iff
      (Module.Flat.lTensor_preserves_injective_linearMap f hf)

@[simp]
theorem pullback_norm (f : F →ₗ[K] E) (hf : Function.Injective f) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.pullback f hf).norm ω x = ξ.norm ω (f.baseChange (S.ϕ ω).Completion x) := rfl

@[simp]
theorem pullback_norm_tmul (f : F →ₗ[K] E) (hf : Function.Injective f) (ω : S.Ω)
    (a : (S.ϕ ω).Completion) (x : F) :
    (ξ.pullback f hf).norm ω (a ⊗ₜ[K] x) = ξ.norm ω (a ⊗ₜ[K] f x) := rfl

@[simp]
theorem pullback_id : ξ.pullback LinearMap.id Function.injective_id = ξ := by
  ext ω x
  simp

/-- Pullback is compatible with composition of injective linear maps. -/
theorem pullback_comp (f : F →ₗ[K] E) (hf : Function.Injective f)
    (g : G →ₗ[K] F) (hg : Function.Injective g) :
    (ξ.pullback f hf).pullback g hg = ξ.pullback (f.comp g) (hf.comp hg) := by
  ext ω x
  simp [LinearMap.baseChange_comp]

/-- Pullback commutes with multiplication by an arbitrary positive function. -/
theorem scale_pullback (a : S.Ω → ℝ) (ha : ∀ ω, 0 < a ω)
    (f : F →ₗ[K] E) (hf : Function.Injective f) :
    (ξ.scale a ha).pullback f hf = (ξ.pullback f hf).scale a ha := by
  ext ω x
  rfl

/-- Pullback preserves the ultrametric inequality at every non-Archimedean place. -/
theorem IsUltrametricAtFinitePlaces.pullback
    {ξ : NormFamily S E} (hξ : ξ.IsUltrametricAtFinitePlaces)
    (f : F →ₗ[K] E)
      (hf : Function.Injective f) : (ξ.pullback f hf).IsUltrametricAtFinitePlaces := by
  constructor
  intro ω hω x y
  simpa only [pullback_norm, map_add] using
    hξ ω hω (f.baseChange (S.ϕ ω).Completion x) (f.baseChange (S.ϕ ω).Completion y)

/-- Restriction to a subspace via the inclusion of its completed scalar extension. -/
noncomputable def restrict (F : Submodule K E) : NormFamily S F :=
  ξ.pullback F.subtype F.subtype_injective

@[simp]
theorem restrict_norm (F : Submodule K E) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.restrict F).norm ω x = ξ.norm ω (F.subtype.baseChange (S.ϕ ω).Completion x) := rfl

@[simp]
theorem restrict_norm_tmul (F : Submodule K E) (ω : S.Ω)
    (a : (S.ϕ ω).Completion) (x : F) :
    (ξ.restrict F).norm ω (a ⊗ₜ[K] x) = ξ.norm ω (a ⊗ₜ[K] (x : E)) := rfl

/-- Positive rescaling and restriction commute. -/
theorem scale_restrict (a : S.Ω → ℝ) (ha : ∀ ω, 0 < a ω) (F : Submodule K E) :
    (ξ.scale a ha).restrict F = (ξ.restrict F).scale a ha :=
  ξ.scale_pullback a ha F.subtype F.subtype_injective

/-- Restriction preserves ultrametricity, including at trivially valued places. -/
theorem IsUltrametricAtFinitePlaces.restrict
    {ξ : NormFamily S E} (hξ : ξ.IsUltrametricAtFinitePlaces)
    (F : Submodule K E) : (ξ.restrict F).IsUltrametricAtFinitePlaces :=
  hξ.pullback F.subtype F.subtype_injective

/-- The restriction to the zero subspace is the unique zero-dimensional norm family. -/
@[simp]
theorem restrict_bot_norm (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] (⊥ : Submodule K E)) :
    (ξ.restrict ⊥).norm ω x = 0 :=
  (ξ.restrict ⊥).norm_eq_zero_of_subsingleton ω x

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NormFamily

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E F : Type*} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

instance instIsUltrametricAtFinitePlacesPullback
    {ξ : NormFamily S E} [hξ : ξ.IsUltrametricAtFinitePlaces]
    (f : F →ₗ[K] E) (hf : Function.Injective f) : (ξ.pullback f hf).IsUltrametricAtFinitePlaces :=
  hξ.pullback f hf

instance instIsUltrametricAtFinitePlacesRestrict
    {ξ : NormFamily S E} [hξ : ξ.IsUltrametricAtFinitePlaces]
    (P : Submodule K E) : (ξ.restrict P).IsUltrametricAtFinitePlaces := hξ.restrict P

end ArakelovGeometry.NormFamily

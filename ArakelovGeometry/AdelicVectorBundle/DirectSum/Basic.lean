/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Basic
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Basic
public import ArakelovGeometry.Analysis.NormShape.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Finiteness.Prod

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Direct sums of norm families

For a family of arbitrary continuous convex shapes from Chen–Moriwaki,
§4.1.1.3 (PDF page 222, printed page 206), construct the direct-sum norm
on each actual completed scalar extension. The canonical tensor-product
product equivalence identifies that fibre with the product of the two fibres.

The inclusions are isometries and the projections are contractive. The max
shape preserves ultrametricity. Hermitian orthogonal sums additionally require
the Archimedean Euclidean shape and are not asserted here.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
variable {E : Type w} [AddCommGroup E] [Module K E]
variable {F : Type w'} [AddCommGroup F] [Module K F]

noncomputable section

variable (ξ : NormFamily S E) (η : NormFamily S F)

/-- The direct-sum norm family for any family of admissible convex profiles.
It is defined on the actual completed fibres of `E × F`. -/
def directSum (ψ : S.Ω → NormShape) : NormFamily S (E × F) where
  norm ω := ((ψ ω).prodSeminorm (ξ.norm ω) (η.norm ω)).comp
    (TensorProduct.prodRight K (S.ϕ ω).Completion (S.ϕ ω).Completion E F).toLinearMap
  norm_eq_zero_iff ω z := by
    rw [Seminorm.comp_apply, (ψ ω).prodSeminorm_eq_zero_iff
      (ξ.norm ω) (η.norm ω) (ξ.norm_eq_zero_iff ω) (η.norm_eq_zero_iff ω)]
    exact (TensorProduct.prodRight K (S.ϕ ω).Completion
      (S.ϕ ω).Completion E F).map_eq_zero_iff

/-- Evaluation through the canonical identification of completed fibres. -/
theorem directSum_norm (ψ : S.Ω → NormShape) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (E × F)) :
    (ξ.directSum η ψ).norm ω z = (ψ ω).perspective
      (ξ.norm ω ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F z).1))
      (η.norm ω ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F z).2)) := rfl

@[simp]
theorem directSum_norm_pair (ψ : S.Ω → NormShape) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.directSum η ψ).norm ω
      ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F).symm (x, y)) =
      (ψ ω).perspective (ξ.norm ω x) (η.norm ω y) := by
  simp only [directSum_norm, LinearEquiv.apply_symm_apply]

@[simp]
theorem directSum_norm_tmul (ψ : S.Ω → NormShape) (ω : S.Ω)
    (a : (S.ϕ ω).Completion) (x : E) (y : F) :
    (ξ.directSum η ψ).norm ω (a ⊗ₜ[K] (x, y)) =
      (ψ ω).perspective (ξ.norm ω (a ⊗ₜ[K] x)) (η.norm ω (a ⊗ₜ[K] y)) := rfl

/-- Different extensions of the same source profiles outside `[0,1]`
produce the same norm family. -/
theorem directSum_congr (ψ χ : S.Ω → NormShape)
    (h : ∀ ω, Set.EqOn (ψ ω).toFun (χ ω).toFun (Set.Icc (0 : ℝ) 1)) :
    ξ.directSum η ψ = ξ.directSum η χ := by
  ext ω z
  simp only [directSum_norm]
  exact (ψ ω).perspective_congr (χ ω) (h ω) (apply_nonneg _ _) (apply_nonneg _ _)

/-- The first completed inclusion is isometric. -/
@[simp]
theorem directSum_norm_inl (ψ : S.Ω → NormShape) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.directSum η ψ).norm ω
      ((LinearMap.inl K E F).baseChange (S.ϕ ω).Completion x) = ξ.norm ω x := by
  have h : TensorProduct.prodRight K (S.ϕ ω).Completion (S.ϕ ω).Completion E F
      ((LinearMap.inl K E F).baseChange (S.ϕ ω).Completion x) = (x, 0) := by
    induction x using TensorProduct.inductionOn with
    | tmul a x => simp
    | add x y hx hy => simp [hx, hy]
  rw [directSum_norm, h]
  simp

/-- The second completed inclusion is isometric. -/
@[simp]
theorem directSum_norm_inr (ψ : S.Ω → NormShape) (ω : S.Ω)
    (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.directSum η ψ).norm ω
      ((LinearMap.inr K E F).baseChange (S.ϕ ω).Completion y) = η.norm ω y := by
  have h : TensorProduct.prodRight K (S.ϕ ω).Completion (S.ϕ ω).Completion E F
      ((LinearMap.inr K E F).baseChange (S.ϕ ω).Completion y) = (0, y) := by
    induction y using TensorProduct.inductionOn with
    | tmul a y => simp
    | add x y hx hy => simp [hx, hy]
  rw [directSum_norm, h]
  simp

/-- Pullback along the first inclusion recovers its given norm family. -/
@[simp]
theorem directSum_pullback_inl (ψ : S.Ω → NormShape) :
    (ξ.directSum η ψ).pullback (LinearMap.inl K E F) LinearMap.inl_injective = ξ := by
  ext ω x
  simp

/-- Pullback along the second inclusion recovers its given norm family. -/
@[simp]
theorem directSum_pullback_inr (ψ : S.Ω → NormShape) :
    (ξ.directSum η ψ).pullback (LinearMap.inr K E F) LinearMap.inr_injective = η := by
  ext ω y
  simp

/-- The first completed projection is contractive. -/
theorem directSum_norm_fst_le (ψ : S.Ω → NormShape) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (E × F)) :
    ξ.norm ω ((LinearMap.fst K E F).baseChange (S.ϕ ω).Completion z) ≤
      (ξ.directSum η ψ).norm ω z := by
  have h : (LinearMap.fst K E F).baseChange (S.ϕ ω).Completion z =
      (TensorProduct.prodRight K (S.ϕ ω).Completion (S.ϕ ω).Completion E F z).1 := by
    induction z using TensorProduct.inductionOn with
    | tmul a z => rfl
    | add z t hz ht => simp [hz, ht]
  rw [h, directSum_norm]
  exact (le_max_left _ _).trans
    ((ψ ω).max_le_perspective (ξ.norm_nonneg ω _) (η.norm_nonneg ω _))

/-- The second completed projection is contractive. -/
theorem directSum_norm_snd_le (ψ : S.Ω → NormShape) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (E × F)) :
    η.norm ω ((LinearMap.snd K E F).baseChange (S.ϕ ω).Completion z) ≤
      (ξ.directSum η ψ).norm ω z := by
  have h : (LinearMap.snd K E F).baseChange (S.ϕ ω).Completion z =
      (TensorProduct.prodRight K (S.ϕ ω).Completion (S.ϕ ω).Completion E F z).2 := by
    induction z using TensorProduct.inductionOn with
    | tmul a z => rfl
    | add z t hz ht => simp [hz, ht]
  rw [h, directSum_norm]
  exact (le_max_right _ _).trans
    ((ψ ω).max_le_perspective (ξ.norm_nonneg ω _) (η.norm_nonneg ω _))

/-- A common positive rescaling commutes with the general direct sum. -/
theorem scale_directSum (ψ : S.Ω → NormShape)
    (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) :
    (ξ.scale f hf).directSum (η.scale f hf) ψ = (ξ.directSum η ψ).scale f hf := by
  ext ω z
  simp only [directSum_norm, scale_norm, NormShape.perspective_mul]

/-- The quotient seminorm along the first projection is exactly the first norm. -/
@[simp]
theorem directSum_quotientSeminorm_fst (ψ : S.Ω → NormShape) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.directSum η ψ).quotientSeminorm (LinearMap.fst K E F)
      LinearMap.fst_surjective ω x = ξ.norm ω x := by
  apply le_antisymm
  · have h := (ξ.directSum η ψ).quotientSeminorm_le (LinearMap.fst K E F)
      LinearMap.fst_surjective ω ((LinearMap.inl K E F).baseChange (S.ϕ ω).Completion x)
    simpa only [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      LinearMap.fst_comp_inl, LinearMap.baseChange_id, LinearMap.id_apply,
      directSum_norm_inl] using h
  · apply ((ξ.directSum η ψ).le_quotientSeminorm_iff _ _ _ _ _).2
    intro z hz
    rw [← hz]
    exact ξ.directSum_norm_fst_le η ψ ω z

/-- The quotient seminorm along the second projection is exactly the second norm. -/
@[simp]
theorem directSum_quotientSeminorm_snd (ψ : S.Ω → NormShape) (ω : S.Ω)
    (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.directSum η ψ).quotientSeminorm (LinearMap.snd K E F)
      LinearMap.snd_surjective ω y = η.norm ω y := by
  apply le_antisymm
  · have h := (ξ.directSum η ψ).quotientSeminorm_le (LinearMap.snd K E F)
      LinearMap.snd_surjective ω ((LinearMap.inr K E F).baseChange (S.ϕ ω).Completion y)
    simpa only [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      LinearMap.snd_comp_inr, LinearMap.baseChange_id, LinearMap.id_apply,
      directSum_norm_inr] using h
  · apply ((ξ.directSum η ψ).le_quotientSeminorm_iff _ _ _ _ _).2
    intro z hz
    rw [← hz]
    exact ξ.directSum_norm_snd_le η ψ ω z

/-- The quotient family along the first projection recovers the first family. -/
@[simp]
theorem directSum_pushforward_fst [FiniteDimensional K E] [FiniteDimensional K F]
    (ψ : S.Ω → NormShape) :
    (ξ.directSum η ψ).pushforward (LinearMap.fst K E F) LinearMap.fst_surjective = ξ := by
  ext ω x
  exact ξ.directSum_quotientSeminorm_fst η ψ ω x

/-- The quotient family along the second projection recovers the second family. -/
@[simp]
theorem directSum_pushforward_snd [FiniteDimensional K E] [FiniteDimensional K F]
    (ψ : S.Ω → NormShape) :
    (ξ.directSum η ψ).pushforward (LinearMap.snd K E F) LinearMap.snd_surjective = η := by
  ext ω y
  exact ξ.directSum_quotientSeminorm_snd η ψ ω y

/-- The direct-sum norm lies between the maximum and the sum of fibre norms. -/
theorem directSum_norm_bounds (ψ : S.Ω → NormShape) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    max (ξ.norm ω x) (η.norm ω y) ≤
        (ξ.directSum η ψ).norm ω
          ((TensorProduct.prodRight K (S.ϕ ω).Completion
            (S.ϕ ω).Completion E F).symm (x, y)) ∧
      (ξ.directSum η ψ).norm ω
          ((TensorProduct.prodRight K (S.ϕ ω).Completion
            (S.ϕ ω).Completion E F).symm (x, y)) ≤ ξ.norm ω x + η.norm ω y := by
  rw [directSum_norm_pair]
  exact ⟨(ψ ω).max_le_perspective (ξ.norm_nonneg ω x) (η.norm_nonneg ω y),
    (ψ ω).perspective_le_add (ξ.norm_nonneg ω x) (η.norm_nonneg ω y)⟩

/-- The max-profile direct sum. -/
def maxDirectSum : NormFamily S (E × F) := ξ.directSum η (fun _ ↦ NormShape.maxShape)

@[simp]
theorem maxDirectSum_norm_pair (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.maxDirectSum η).norm ω
      ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F).symm (x, y)) = max (ξ.norm ω x) (η.norm ω y) := by
  simp [maxDirectSum, ξ.norm_nonneg, η.norm_nonneg]

/-- It suffices for the profiles to agree with the max shape on `[0,1]`
at non-Archimedean places; their extensions to the real line are irrelevant. -/
theorem IsUltrametricAtFinitePlaces.directSum_of_profile_eq_max
    {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsUltrametricAtFinitePlaces) (hη : η.IsUltrametricAtFinitePlaces) (ψ : S.Ω → NormShape)
    (hψ : ∀ ω ∈ S.Ωfin,
      Set.EqOn (ψ ω).toFun NormShape.maxShape.toFun (Set.Icc (0 : ℝ) 1)) :
    (ξ.directSum η ψ).IsUltrametricAtFinitePlaces := by
  constructor
  intro ω hω z t
  have hshape {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
      (ψ ω).perspective a b = max a b :=
    ((ψ ω).perspective_congr NormShape.maxShape (hψ ω hω) ha hb).trans
      (NormShape.maxShape_perspective ha hb)
  let e := TensorProduct.prodRight K (S.ϕ ω).Completion (S.ϕ ω).Completion E F
  have h := max_le_max (hξ ω hω (e z).1 (e t).1) (hη ω hω (e z).2 (e t).2)
  rw [max_max_max_comm] at h
  simpa only [directSum_norm, hshape (apply_nonneg _ _) (apply_nonneg _ _),
    map_add, Prod.fst_add, Prod.snd_add] using h

/-- Max shapes at the non-Archimedean places preserve ultrametricity. -/
theorem IsUltrametricAtFinitePlaces.directSum {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsUltrametricAtFinitePlaces) (hη : η.IsUltrametricAtFinitePlaces) (ψ : S.Ω → NormShape)
    (hψ : ∀ ω ∈ S.Ωfin, ψ ω = NormShape.maxShape) :
    (ξ.directSum η ψ).IsUltrametricAtFinitePlaces := by
  apply hξ.directSum_of_profile_eq_max hη ψ
  intro ω hω
  rw [hψ ω hω]
  exact fun _ _ ↦ rfl

/-- The max direct sum of ultrametric norm families is ultrametric. -/
theorem IsUltrametricAtFinitePlaces.maxDirectSum {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsUltrametricAtFinitePlaces)
      (hη : η.IsUltrametricAtFinitePlaces) : (ξ.maxDirectSum η).IsUltrametricAtFinitePlaces :=
  hξ.directSum hη (fun _ ↦ NormShape.maxShape) (fun _ _ ↦ rfl)

/-- When the second space is zero-dimensional, the norm is the first norm. -/
theorem directSum_norm_pair_of_subsingleton_right [Subsingleton F]
    (ψ : S.Ω → NormShape) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.directSum η ψ).norm ω
      ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F).symm (x, y)) = ξ.norm ω x := by
  simp [η.norm_eq_zero_of_subsingleton]

/-- When the first space is zero-dimensional, the norm is the second norm. -/
theorem directSum_norm_pair_of_subsingleton_left [Subsingleton E]
    (ψ : S.Ω → NormShape) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.directSum η ψ).norm ω
      ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F).symm (x, y)) = η.norm ω y := by
  simp [ξ.norm_eq_zero_of_subsingleton]

end

end ArakelovGeometry.NormFamily

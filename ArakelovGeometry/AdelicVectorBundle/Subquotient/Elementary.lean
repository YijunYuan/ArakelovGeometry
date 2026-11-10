/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Discrepancy.Majorant.Basic
import ArakelovGeometry.Analysis.NormedSpace.FiniteDimensional
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Elementary norms on actual completed subquotients

The elementary condition at a chosen fibre is preserved by injective
pullback and surjective pushforward. Only that fibre is constrained.
The quotient norm remains the existing completed-kernel quotient norm,
and the proofs include zero sources, zero targets, and zero subspaces.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]
  {F : Type w'} [AddCommGroup F] [Module K F]
  {η : NormFamily S E}
  {hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion} {ω : S.Ω}

/-- Injective pullback preserves the elementary condition at the chosen
actual fibre, without imposing conditions at other places. -/
theorem IsElementaryAt.pullback (he : η.IsElementaryAt hN ω)
    (f : F →ₗ[K] E) (hf : Function.Injective f) :
    (η.pullback f hf).IsElementaryAt hN ω := by
  refine ⟨fun hω x y => ?_, fun hω => ?_⟩
  · simpa only [pullback_norm, map_add] using
      he.1 hω (f.baseChange (S.ϕ ω).Completion x) (f.baseChange (S.ϕ ω).Completion y)
  · let := hN ω hω
    let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    let := η.fibreNormedAddCommGroup ω
    let := η.fibreNormedSpace ω
    let := (η.pullback f hf).fibreNormedAddCommGroup ω
    let := (η.pullback f hf).fibreNormedSpace ω
    have : InnerProductSpaceable ((S.ϕ ω).Completion ⊗[K] E) :=
      exists_innerProductCore_iff_innerProductSpaceable.mp (he.2 hω)
    apply exists_innerProductCore_iff_innerProductSpaceable.mpr
    exact innerProductSpaceable_of_norm_preserving_addMonoidHom
      (f.baseChange (S.ϕ ω).Completion).toAddMonoidHom (fun _ => rfl)

/-- Every actual completed subspace inherits the chosen-fibre elementary
condition, including the zero and whole subspaces. -/
theorem IsElementaryAt.restrict (he : η.IsElementaryAt hN ω) (W : Submodule K E) :
    (η.restrict W).IsElementaryAt hN ω :=
  he.pullback W.subtype W.subtype_injective

variable [FiniteDimensional K E]

/-- A local ultrametric inequality passes to the actual completed quotient
norm by nearly optimal lifts. No global ultrametric hypothesis is required. -/
theorem pushforward_norm_add_le_max_of_norm_add_le_max (ξ : NormFamily S E)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π) (ω : S.Ω)
    (hu : ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y))
    (z t : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.pushforward π hπ).norm ω (z + t) ≤
      max ((ξ.pushforward π hπ).norm ω z) ((ξ.pushforward π hπ).norm ω t) := by
  change ξ.quotientSeminorm π hπ ω (z + t) ≤
    max (ξ.quotientSeminorm π hπ ω z) (ξ.quotientSeminorm π hπ ω t)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, hn⟩ := ξ.exists_quotientSeminorm_lift_lt π hπ ω z hε
  obtain ⟨y, hy, hm⟩ := ξ.exists_quotientSeminorm_lift_lt π hπ ω t hε
  calc
    ξ.quotientSeminorm π hπ ω (z + t) =
        ξ.quotientSeminorm π hπ ω (π.baseChange (S.ϕ ω).Completion (x + y)) := by
      rw [(π.baseChange (S.ϕ ω).Completion).map_add, hx, hy]
    _ ≤ ξ.norm ω (x + y) := ξ.quotientSeminorm_le π hπ ω (x + y)
    _ ≤ max (ξ.norm ω x) (ξ.norm ω y) := hu x y
    _ ≤ max (ξ.quotientSeminorm π hπ ω z + ε)
        (ξ.quotientSeminorm π hπ ω t + ε) := max_le_max hn.le hm.le
    _ = max (ξ.quotientSeminorm π hπ ω z) (ξ.quotientSeminorm π hπ ω t) + ε :=
      max_add_add_right _ _ _

/-- Surjective pushforward preserves the elementary condition at the chosen
fibre. At infinity, the inner product is inherited from the actual
completed-kernel quotient with its prescribed quotient norm. -/
theorem IsElementaryAt.pushforward (he : η.IsElementaryAt hN ω)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π) :
    (η.pushforward π hπ).IsElementaryAt hN ω := by
  refine ⟨fun hω x y =>
    η.pushforward_norm_add_le_max_of_norm_add_le_max π hπ ω (he.1 hω) x y,
    fun hω => ?_⟩
  let := hN ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := η.fibreNormedAddCommGroup ω
  let := η.fibreNormedSpace ω
  let := (η.pushforward π hπ).fibreNormedAddCommGroup ω
  let := (η.pushforward π hπ).fibreNormedSpace ω
  obtain ⟨c, hc⟩ := he.2 hω
  let := innerProductSpaceOfCoreNorm c hc
  let W := (π.baseChange (S.ϕ ω).Completion).ker
  have : IsClosed (W : Set ((S.ϕ ω).Completion ⊗[K] E)) :=
    finiteDimensional_submodule_isClosed W
  have : InnerProductSpaceable (((S.ϕ ω).Completion ⊗[K] E) ⧸ W) :=
    InnerProductSpace.toInnerProductSpaceable (S.ϕ ω).Completion
  let e := (π.baseChange (S.ϕ ω).Completion).quotKerEquivOfSurjective
    (LinearMap.baseChange_surjective _ hπ)
  apply exists_innerProductCore_iff_innerProductSpaceable.mpr
  exact innerProductSpaceable_of_norm_preserving_addMonoidHom
    e.symm.toLinearMap.toAddMonoidHom (fun _ => rfl)

/-- Quotient by any actual subspace preserves the chosen-fibre elementary
condition, including both zero-dimensional ends. -/
theorem IsElementaryAt.quotient (he : η.IsElementaryAt hN ω) (W : Submodule K E) :
    (η.quotient W).IsElementaryAt hN ω :=
  he.pushforward W.mkQ W.mkQ_surjective

end

end ArakelovGeometry.NormFamily

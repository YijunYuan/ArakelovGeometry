---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AbsoluteValue.exists_extension
docstring: 'Every real absolute value extends to every algebraic field extension.

  This is the absolute-value extension used in Chen–Moriwaki, Proposition 3.4.5.'
file: ArakelovGeometry/ExternalResults/AbsoluteValueExtension.lean
generated: lean
lean_status: lean_ok
title: AbsoluteValue.exists_extension
type: lean
updated: '2026-10-02T11:55:12'
---
theorem exists_extension {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (v : AbsoluteValue K ℝ) :
    ∃ w : AbsoluteValue L ℝ, w.restriction K = v := by
  let F := v.Completion
  let u : AbsoluteValue F ℝ := NormedField.toAbsoluteValue F
  let e : WithAbs u ≃ᵢ F := {
    (WithAbs.equiv u).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv u)
      (fun _ ↦ rfl) }
  have : CompleteSpace (WithAbs u) := e.completeSpace
  obtain ⟨w, hw, -⟩ := existsUnique_extension_of_complete (L := AlgebraicClosure F) u
  let i : L →ₐ[K] AlgebraicClosure F := IsAlgClosed.lift
  refine ⟨w.pullback i.toRingHom, ?_⟩
  ext a
  change w (i (algebraMap K L a)) = v a
  rw [i.commutes]
  rw [IsScalarTower.algebraMap_apply K F (AlgebraicClosure F)]
  rw [show w (algebraMap F (AlgebraicClosure F) (algebraMap K F a)) =
      u (algebraMap K F a) from
    congrArg (fun z : AbsoluteValue F ℝ ↦ z (algebraMap K F a)) hw]
  exact UniformSpace.Completion.norm_coe (WithAbs.toAbs v a)
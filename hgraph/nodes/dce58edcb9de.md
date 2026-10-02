---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AbsoluteValue.finite_extensions
docstring: A real absolute value has only finitely many extensions to a finite field
  extension.
file: ArakelovGeometry/ExternalResults/AbsoluteValueFinite.lean
generated: lean
lean_status: lean_ok
title: AbsoluteValue.finite_extensions
type: lean
updated: '2026-10-02T11:55:12'
---
theorem finite_extensions {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (v : AbsoluteValue K ℝ) :
    Set.Finite {w : AbsoluteValue L ℝ | w.restriction K = v} := by
  let B := v.Completion
  let n : AbsoluteValue B ℝ := NormedField.toAbsoluteValue B
  let e : WithAbs n ≃ᵢ B := {
    (WithAbs.equiv n).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv n) (fun _ ↦ rfl) }
  have : CompleteSpace (WithAbs n) := e.completeSpace
  obtain ⟨u, hu, -⟩ := existsUnique_extension_of_complete (L := AlgebraicClosure B) n
  refine (Set.finite_range
    (fun σ : L →ₐ[K] AlgebraicClosure B ↦ u.pullback σ.toRingHom)).subset ?_
  intro w hw
  obtain ⟨σ, hσ⟩ := exists_algHom_eq_pullback v w hw u hu
  exact ⟨σ, hσ.symm⟩
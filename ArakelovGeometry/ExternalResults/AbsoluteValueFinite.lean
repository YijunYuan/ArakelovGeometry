/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.ExternalResults.AbsoluteValueExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Finiteness of extending absolute values

Every absolute value on a finite field extension is realized by an embedding into an
algebraic closure of the completed base. The finite set of algebra embeddings therefore
parametrizes all extending absolute values, as required in Chen–Moriwaki, §3.3.
-/

namespace AbsoluteValue

/-- An extending absolute value is the pullback of the value on an algebraic closure
of the completed base along a field embedding. -/
theorem exists_algHom_eq_pullback {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (hw : w.restriction K = v)
    (u : AbsoluteValue (AlgebraicClosure v.Completion) ℝ)
    (hu : u.restriction v.Completion = NormedField.toAbsoluteValue v.Completion) :
    ∃ σ : L →ₐ[K] AlgebraicClosure v.Completion, w = u.pullback σ.toRingHom := by
  subst v
  let B := (w.restriction K).Completion
  let C := AlgebraicClosure B
  have : FiniteDimensional B w.Completion := finiteDimensional_completion w K
  have : IsScalarTower K B w.Completion := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change ((WithAbs.toAbs w (algebraMap K L x)) : w.Completion) = _
    rw [algebraMap_completion_def]
    exact (UniformSpace.Completion.mapRingHom_coe
      (isometry_algebraMap_withAbs w K).continuous (WithAbs.toAbs (w.restriction K) x)).symm
  let i : w.Completion →ₐ[B] C := IsAlgClosed.lift
  let j : L →ₐ[K] w.Completion := {
    toRingHom := UniformSpace.Completion.coeRingHom.comp (WithAbs.equiv w).symm.toRingHom
    commutes' _ := rfl }
  let n : AbsoluteValue B ℝ := NormedField.toAbsoluteValue B
  let e : WithAbs n ≃ᵢ B := {
    (WithAbs.equiv n).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv n) (fun _ ↦ rfl) }
  have : CompleteSpace (WithAbs n) := e.completeSpace
  have hni : (u.pullback i.toRingHom).restriction B = n := by
    ext x
    change u (i (algebraMap B w.Completion x)) = ‖x‖
    rw [i.commutes]
    exact congrArg (fun z : AbsoluteValue B ℝ ↦ z x) hu
  have hnn : (NormedField.toAbsoluteValue w.Completion).restriction B = n := by
    ext x
    exact norm_algebraMap_completion w K x
  have heq := (existsUnique_extension_of_complete (L := w.Completion) n).unique hni hnn
  refine ⟨(i.restrictScalars K).comp j, ?_⟩
  ext x
  have h := congrArg (fun z : AbsoluteValue w.Completion ℝ ↦ z (j x)) heq
  change w x = u (i (j x))
  change u (i (j x)) = ‖(WithAbs.toAbs w x : w.Completion)‖ at h
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs] at h
  exact h.symm

/-- A real absolute value has only finitely many extensions to a finite field extension. -/
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

end AbsoluteValue

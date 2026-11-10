/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.ExternalResults.AbsoluteValueExtension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Finiteness of extending absolute values

Every absolute value on a finite field extension is realized by an embedding into an
algebraic closure of the completed base. The finite set of algebra embeddings therefore
parametrizes all extending absolute values, as required in Chen–Moriwaki, §3.3.
-/

@[expose] public section

namespace AbsoluteValue

/-- An extending absolute value is the pullback of the value on an algebraic closure
of the completed base along a field embedding. -/
theorem exists_algHom_eq_pullback {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (hw : w.under K = v)
    (u : AbsoluteValue (AlgebraicClosure v.Completion) ℝ)
    (hu : u.under v.Completion = NormedField.toAbsoluteValue v.Completion) :
    ∃ σ : L →ₐ[K] AlgebraicClosure v.Completion, w = u.comp σ.toRingHom.injective := by
  subst v
  let B := (w.under K).Completion
  let C := AlgebraicClosure B
  have : FiniteDimensional B w.Completion := finiteDimensional_completion w K
  have : IsScalarTower K B w.Completion := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change ((WithAbs.toAbs w (algebraMap K L x)) : w.Completion) = _
    rw [AbsoluteValue.Completion.algebraMap_eq]
    exact (UniformSpace.Completion.mapRingHom_coe
      (WithAbs.isometry_map (w.under K) w).continuous (WithAbs.toAbs (w.under K) x)).symm
  let i : w.Completion →ₐ[B] C := IsAlgClosed.lift
  let j : L →ₐ[K] w.Completion := {
    toRingHom := UniformSpace.Completion.coeRingHom.comp (WithAbs.equiv w).symm.toRingHom
    commutes' _ := rfl }
  let n : AbsoluteValue B ℝ := NormedField.toAbsoluteValue B
  let e : WithAbs n ≃ᵢ B := {
    (WithAbs.equiv n).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv n) (fun _ ↦ rfl) }
  have : CompleteSpace (WithAbs n) := e.completeSpace
  have hni : (u.comp i.toRingHom.injective).under B = n := by
    ext x
    change u (i (algebraMap B w.Completion x)) = ‖x‖
    rw [i.commutes]
    exact congrArg (fun z : AbsoluteValue B ℝ ↦ z x) hu
  have hnn : (NormedField.toAbsoluteValue w.Completion).under B = n := by
    ext x
    exact norm_algebraMap' w.Completion x
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
    Set.Finite {w : AbsoluteValue L ℝ | w.under K = v} := by
  let B := v.Completion
  let n : AbsoluteValue B ℝ := NormedField.toAbsoluteValue B
  let e : WithAbs n ≃ᵢ B := {
    (WithAbs.equiv n).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv n) (fun _ ↦ rfl) }
  have : CompleteSpace (WithAbs n) := e.completeSpace
  obtain ⟨u, hu, -⟩ := existsUnique_extension_of_complete (L := AlgebraicClosure B) n
  refine (Set.finite_range
    (fun σ : L →ₐ[K] AlgebraicClosure B ↦ u.comp σ.toRingHom.injective)).subset ?_
  intro w hw
  obtain ⟨σ, hσ⟩ := exists_algHom_eq_pullback v w hw u hu
  exact ⟨σ, hσ.symm⟩

/-- A finite separable field extension remains separable after completion. -/
theorem isSeparable_completion {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (w : AbsoluteValue L ℝ) :
    Algebra.IsSeparable (w.under K).Completion w.Completion := by
  let B := (w.under K).Completion
  have : IsScalarTower K B w.Completion := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change ((WithAbs.toAbs w (algebraMap K L x)) : w.Completion) = _
    rw [AbsoluteValue.Completion.algebraMap_eq]
    exact (UniformSpace.Completion.mapRingHom_coe
      (WithAbs.isometry_map (w.under K) w).continuous (WithAbs.toAbs (w.under K) x)).symm
  let j : L →ₐ[K] w.Completion := {
    toRingHom := UniformSpace.Completion.coeRingHom.comp (WithAbs.equiv w).symm.toRingHom
    commutes' _ := rfl }
  let b := Module.Free.chooseBasis K L
  have hspan : Submodule.span B (Set.range fun i ↦ (WithAbs.toAbs w (b i) : w.Completion)) ≤
      (separableClosure B w.Completion).toSubalgebra.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply mem_separableClosure_iff.mpr
    exact (IsSeparable.map j j.injective (Algebra.IsSeparable.isSeparable K (b i))).tower_top B
  rw [span_coe_basis_eq_top w K b] at hspan
  exact ⟨fun x ↦ mem_separableClosure_iff.mp (hspan Submodule.mem_top)⟩

/-- Every absolute value has at least one extension to a finite field extension. -/
theorem natCard_extensions_pos {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (v : AbsoluteValue K ℝ) :
    0 < Nat.card {w : AbsoluteValue L ℝ // w.under K = v} := by
  have : Finite {w : AbsoluteValue L ℝ // w.under K = v} :=
    (finite_extensions (L := L) v).to_subtype
  obtain ⟨w, hw⟩ := exists_extension (L := L) v
  have : Nonempty {w : AbsoluteValue L ℝ // w.under K = v} := ⟨⟨w, hw⟩⟩
  exact Nat.card_pos

/-- The number of extending absolute values is bounded by the degree of the field extension. -/
theorem natCard_extensions_le_finrank {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (v : AbsoluteValue K ℝ) :
    Nat.card {w : AbsoluteValue L ℝ // w.under K = v} ≤ Module.finrank K L := by
  classical
  let B := v.Completion
  let n : AbsoluteValue B ℝ := NormedField.toAbsoluteValue B
  let e : WithAbs n ≃ᵢ B := {
    (WithAbs.equiv n).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv n) (fun _ ↦ rfl) }
  have : CompleteSpace (WithAbs n) := e.completeSpace
  obtain ⟨u, hu, -⟩ := existsUnique_extension_of_complete (L := AlgebraicClosure B) n
  choose f hf using fun w : {w : AbsoluteValue L ℝ // w.under K = v} ↦
    exists_algHom_eq_pullback v w.val w.property u hu
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    rw [hf x, hf y, h]
  exact (Nat.card_le_card_of_injective f hinj).trans
    (card_algHom_le_finrank K L (AlgebraicClosure B))

end AbsoluteValue

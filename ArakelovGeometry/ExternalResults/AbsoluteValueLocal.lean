/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.ExternalResults.AbsoluteValueFinite
import Mathlib.FieldTheory.PrimitiveElement

/-!
# The sum of local degrees

Embeddings of a finite extension into an algebraic closure of the completed base
are partitioned by the absolute values they induce. The embeddings in each part
are exactly the embeddings of the corresponding completed extension. Counting
them gives the local-degree sum of Chen–Moriwaki, §3.3, formula (3.3).
-/

open UniformSpace

namespace AbsoluteValue

/-- Every embedding into the algebraic closure of the completed base that induces
`w` extends uniquely to the completion at `w`. -/
theorem existsUnique_completion_algHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (w : AbsoluteValue L ℝ)
    (u : AbsoluteValue (AlgebraicClosure (w.restriction K).Completion) ℝ)
    (hu : u.restriction (w.restriction K).Completion =
      NormedField.toAbsoluteValue (w.restriction K).Completion)
    (σ : L →ₐ[K] AlgebraicClosure (w.restriction K).Completion)
    (hσ : u.pullback σ.toRingHom = w) :
    ∃! τ : w.Completion →ₐ[(w.restriction K).Completion]
        AlgebraicClosure (w.restriction K).Completion,
      ∀ x : L, τ (algebraMap L w.Completion x) = σ x := by
  let B := (w.restriction K).Completion
  let C := AlgebraicClosure B
  have : FiniteDimensional B w.Completion := finiteDimensional_completion w K
  let f : WithAbs w →+* WithAbs u := WithAbs.map w u σ.toRingHom
  have hf : Isometry f := AddMonoidHomClass.isometry_of_norm f (fun x ↦ by
    exact congrArg (fun z : AbsoluteValue L ℝ ↦ z x.ofAbs) hσ)
  let h : w.Completion →+* u.Completion := hf.mapRingHom
  have hb : Isometry (algebraMap B u.Completion) :=
    AddMonoidHomClass.isometry_of_norm (algebraMap B u.Completion) fun b ↦ by
      change ‖(WithAbs.toAbs u (algebraMap B C b) : u.Completion)‖ = ‖b‖
      rw [Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs]
      exact congrArg (fun z : AbsoluteValue B ℝ ↦ z b) hu
  have hcomm (b : B) : h (algebraMap B w.Completion b) = algebraMap B u.Completion b := by
    induction b using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (hf.isometry_mapRingHom.continuous.comp (isometry_algebraMap_completion w K).continuous)
        hb.continuous
    | ih a =>
      rw [algebraMap_completion_def, Completion.mapRingHom_coe, Isometry.mapRingHom_coe]
      change (WithAbs.toAbs u (σ (algebraMap K L a.ofAbs)) : u.Completion) =
        algebraMap B u.Completion (a : B)
      rw [σ.commutes]
      rfl
  let ha : w.Completion →ₐ[B] u.Completion := { h with commutes' := hcomm }
  let e := Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits
    (F := B) (K := w.Completion) u.Completion C (fun _ ↦ IsAlgClosed.splits _)
  have he (x : L) : e.symm ha (algebraMap L w.Completion x) = σ x := by
    apply (algebraMap C u.Completion).injective
    change e (e.symm ha) (algebraMap L w.Completion x) =
      algebraMap C u.Completion (σ x)
    rw [e.apply_symm_apply]
    exact hf.mapRingHom_coe (WithAbs.toAbs w x)
  refine ⟨e.symm ha, he, fun τ hτ ↦ ?_⟩
  have heq : τ.toLinearMap = (e.symm ha).toLinearMap :=
    LinearMap.ext_on_range (span_coe_basis_eq_top w K (Module.Free.chooseBasis K L))
      (fun i ↦ (hτ _).trans (he _).symm)
  ext x
  exact LinearMap.congr_fun heq x

/-- An embedding of a completed finite extension into an algebraic closure
preserves the unique extending absolute value. -/
theorem apply_completion_algHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (w : AbsoluteValue L ℝ)
    (u : AbsoluteValue (AlgebraicClosure (w.restriction K).Completion) ℝ)
    (hu : u.restriction (w.restriction K).Completion =
      NormedField.toAbsoluteValue (w.restriction K).Completion)
    (τ : w.Completion →ₐ[(w.restriction K).Completion]
      AlgebraicClosure (w.restriction K).Completion) (x : w.Completion) :
    u (τ x) = ‖x‖ := by
  let B := (w.restriction K).Completion
  have : FiniteDimensional B w.Completion := finiteDimensional_completion w K
  let n : AbsoluteValue B ℝ := NormedField.toAbsoluteValue B
  let e : WithAbs n ≃ᵢ B := {
    (WithAbs.equiv n).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv n) (fun _ ↦ rfl) }
  have : CompleteSpace (WithAbs n) := e.completeSpace
  have ht : (u.pullback τ.toRingHom).restriction B = n := by
    ext b
    change u (τ (algebraMap B w.Completion b)) = ‖b‖
    rw [τ.commutes]
    exact congrArg (fun z : AbsoluteValue B ℝ ↦ z b) hu
  have hn : (NormedField.toAbsoluteValue w.Completion).restriction B = n := by
    ext b
    exact norm_algebraMap_completion w K b
  exact congrArg (fun z : AbsoluteValue w.Completion ℝ ↦ z x)
    ((existsUnique_extension_of_complete (L := w.Completion) n).unique ht hn)

end AbsoluteValue

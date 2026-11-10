/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.OperatorNorm
public import ArakelovGeometry.AdelicVectorBundle.Tensor
public import ArakelovGeometry.AdelicVectorBundle.TensorOperatorBaseChange

/-!
# Completed injective tensor and operator identities

All norms below live on the canonical completed scalar extensions. Evaluation
identifies the relevant bidual norm with the operator norm on the local dual.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}

/-- Completed bidual evaluation is the actual operator norm on the local dual. -/
theorem dual_dual_norm_eval_eq_operator {V : Type w} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ξ : NormFamily S V) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] V) :
    let := ξ.fibreNormedAddCommGroup ω
    let := ξ.fibreNormedSpace ω
    let := linearDualNormedAddCommGroup (k := (S.ϕ ω).Completion)
      (E := (S.ϕ ω).Completion ⊗[K] V)
    let := linearDualNormedSpace (k := (S.ϕ ω).Completion)
      (E := (S.ϕ ω).Completion ⊗[K] V)
    ξ.dual.dual.norm ω ((Module.Dual.eval K V).baseChange (S.ϕ ω).Completion x) =
      linearMapOperatorSeminorm
        (Module.Dual.eval (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] V) x) := by
  intro fibreGroup fibreSpace dualGroup dualSpace
  let := fibreGroup
  let := fibreSpace
  let := dualGroup
  let := dualSpace
  have hn (f : Module.Dual (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] V)) :
      ‖f‖ = linearMapOperatorSeminorm f := rfl
  rw [ξ.dual.dual_norm_eq_sSup, linearMapOperatorSeminorm_eq_sSup]
  congr 1
  ext r
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨dualBaseChangeEquiv K (S.ϕ ω).Completion V f, ?_⟩
    simpa only [dualBaseChangeEquiv_eval, LinearEquiv.dualMap_apply,
      Module.Dual.eval_apply, hn, dual, dualSeminorm, Seminorm.comp_apply,
      LinearEquiv.coe_coe] using hf
  · rintro ⟨f, hf⟩
    refine ⟨(dualBaseChangeEquiv K (S.ϕ ω).Completion V).symm f, ?_⟩
    simpa only [dualBaseChangeEquiv_eval, LinearEquiv.dualMap_apply,
      Module.Dual.eval_apply, dual, dualSeminorm, Seminorm.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hn] using hf

variable {E : Unit ⊕ Unit → Type w} [∀ i, AddCommGroup (E i)]
  [∀ i, Module K (E i)] [∀ i, FiniteDimensional K (E i)]

/-- On rational tensors the completed injective norm is the operator norm
from the first dual family to the second canonical bidual family. -/
theorem injectiveTensor_norm_eq_operatorNorm (ξ : ∀ i, NormFamily S (E i))
    (ω : S.Ω) (z : ⨂[K] i, E i) :
    (injectiveTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z) =
      (ξ (.inl ())).dual.operatorNorm
        ((ξ (.inr ())).dual.dual.pullback (Module.Dual.eval K (E (.inr ())))
          (Module.eval_apply_injective K)) ω (binaryTensorToHom K E z) := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i ↦ (ξ i).fibreNormedSpace ω
  let := linearDualNormedAddCommGroup (k := (S.ϕ ω).Completion)
    (E := (S.ϕ ω).Completion ⊗[K] E (.inl ()))
  let := linearDualNormedSpace (k := (S.ϕ ω).Completion)
    (E := (S.ϕ ω).Completion ⊗[K] E (.inl ()))
  let := linearDualNormedAddCommGroup (k := (S.ϕ ω).Completion)
    (E := (S.ϕ ω).Completion ⊗[K] E (.inr ()))
  let := linearDualNormedSpace (k := (S.ϕ ω).Completion)
    (E := (S.ϕ ω).Completion ⊗[K] E (.inr ()))
  let := linearDualNormedAddCommGroup (k := (S.ϕ ω).Completion)
    (E := Module.Dual (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E (.inr ())))
  let := linearDualNormedSpace (k := (S.ϕ ω).Completion)
    (E := Module.Dual (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E (.inr ())))
  let t := tensorBaseChangeEquiv K (S.ϕ ω).Completion E
    ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z)
  let T := binaryTensorOperator (S.ϕ ω).Completion
    (fun i ↦ (S.ϕ ω).Completion ⊗[K] E i) t
  let e := dualBaseChangeEquiv K (S.ϕ ω).Completion (E (.inl ()))
  have hs (x : (S.ϕ ω).Completion ⊗[K] Module.Dual K (E (.inl ()))) :
      ‖e x‖ = (ξ (.inl ())).dual.norm ω x := rfl
  have ht (x : (S.ϕ ω).Completion ⊗[K] Module.Dual K (E (.inl ()))) :
      ‖T (e x)‖ = (ξ (.inr ())).dual.dual.norm ω
        ((Module.Dual.eval K (E (.inr ()))).baseChange (S.ϕ ω).Completion
          ((binaryTensorToHom K E z).baseChange (S.ϕ ω).Completion x)) := by
    dsimp only [T]
    rw [binaryTensorOperator_eq_eval]
    change linearMapOperatorSeminorm (Module.Dual.eval (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E (.inr ()))
      (binaryTensorToHom (S.ϕ ω).Completion
        (fun i ↦ (S.ϕ ω).Completion ⊗[K] E i) t (e x))) = _
    rw [binaryTensorToHom_baseChange]
    exact ((ξ (.inr ())).dual_dual_norm_eval_eq_operator ω _).symm
  calc
    (injectiveTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z) =
        linearMapOperatorSeminorm T := injectiveTensorSeminorm_eq_binaryTensorOperator t
    _ = _ := by
      rw [linearMapOperatorSeminorm_eq_sSup, operatorNorm_eq_sSup]
      congr 1
      ext r
      constructor
      · rintro ⟨f, hf⟩
        obtain ⟨x, rfl⟩ := e.surjective f
        refine ⟨x, ?_⟩
        simpa only [ht, hs, pullback_norm] using hf
      · rintro ⟨x, hx⟩
        refine ⟨e x, ?_⟩
        simpa only [ht, hs, pullback_norm] using hx

end

end ArakelovGeometry.NormFamily

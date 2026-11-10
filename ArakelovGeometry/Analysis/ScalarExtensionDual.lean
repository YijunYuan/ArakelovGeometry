/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DualBaseChange
public import ArakelovGeometry.Analysis.ScalarExtensionNorm

/-!
# Dual norms under scalar extension

The operator norm on the actual algebraic dual commutes with injective
scalar extension over complete non-Archimedean fields.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable {k E : Type*} [NormedField k] [CompleteSpace k]
  [NormedAddCommGroup E] [NormedSpace k E] [FiniteDimensional k E]

/-- The existing algebraic dual, equipped with the separated operator norm.
This also applies to complete trivially normed scalar fields. -/
abbrev linearDualNormedAddCommGroup : NormedAddCommGroup (Module.Dual k E) :=
  (⟨(linearMapOperatorSeminorm (L := k) (V := E) (W := k)).toAddGroupSeminorm,
    fun f ↦ (linearMapOperatorSeminorm_eq_zero_iff f).mp⟩ :
    AddGroupNorm (Module.Dual k E)).toNormedAddCommGroup

/-- The operator norm respects the original scalar action on the algebraic dual. -/
abbrev linearDualNormedSpace :
    let := linearDualNormedAddCommGroup (k := k) (E := E)
    NormedSpace k (Module.Dual k E) := by
  let := linearDualNormedAddCommGroup (k := k) (E := E)
  exact ⟨fun a f ↦ (map_smul_eq_mul linearMapOperatorSeminorm a f).le⟩

variable {L : Type*} [NormedField L] [NormedAlgebra k L]

omit [CompleteSpace k] in
/-- Canonical base change of a rational dual vector is its extended evaluation. -/
theorem dualBaseChangeEquiv_one_tmul (f : Module.Dual k E) :
    dualBaseChangeEquiv k L E ((1 : L) ⊗ₜ[k] f) = scalarExtensionDualEval f := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  simp only [dualBaseChangeEquiv_tmul_apply_tmul, one_mul, scalarExtensionDualEval_tmul]

/-- Extending evaluation on the algebraic dual agrees with the actual
scalar-extension pairing evaluated at a rational vector. -/
theorem scalarExtensionDualEval_eval (x : E) (z : L ⊗[k] Module.Dual k E) :
    let := linearDualNormedAddCommGroup (k := k) (E := E)
    let := linearDualNormedSpace (k := k) (E := E)
    scalarExtensionDualEval (Module.Dual.eval k E x) z =
      dualBaseChangeEquiv k L E z ((1 : L) ⊗ₜ[k] x) := by
  intro dualGroup dualSpace
  let := dualGroup
  let := dualSpace
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hz ht
  | tmul a f => simp only [scalarExtensionDualEval_tmul,
      dualBaseChangeEquiv_tmul_apply_tmul, mul_one, Module.Dual.eval_apply]

/-- The rational injective-extension norm is exactly the norm of evaluation
on the operator-normed algebraic dual. -/
theorem scalarExtensionInjectiveSeminorm_one_tmul_eq_eval_norm (x : E) :
    let := linearDualNormedAddCommGroup (k := k) (E := E)
    let := linearDualNormedSpace (k := k) (E := E)
    scalarExtensionInjectiveSeminorm ((1 : L) ⊗ₜ[k] x) =
      linearMapOperatorSeminorm (Module.Dual.eval k E x) := by
  intro dualGroup dualSpace
  let := dualGroup
  let := dualSpace
  rw [scalarExtensionInjectiveSeminorm_one_tmul, linearMapOperatorSeminorm_eq_sSup]
  rfl

/-- Under canonical dual base change, the dual of the injective extension
is the injective extension of the dual norm. The original vector norm need
not be ultrametric, and complete trivially valued fields are included. -/
theorem scalarExtensionInjective_dual [CompleteSpace L] [IsUltrametricDist L]
    (z : L ⊗[k] Module.Dual k E) :
    let := linearDualNormedAddCommGroup (k := k) (E := E)
    let := linearDualNormedSpace (k := k) (E := E)
    let r := scalarExtensionInjectiveSeminorm (k := k) (L := L) (E := Module.Dual k E)
    let := scalarExtensionInjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
    let := scalarExtensionInjectiveNormedSpace (k := k) (L := L) (E := E)
    linearMapOperatorSeminorm (dualBaseChangeEquiv k L E z) = r z := by
  intro dualGroup dualSpace r extGroup extSpace
  let := dualGroup
  let := dualSpace
  let := extGroup
  let := extSpace
  let qd : Seminorm L (L ⊗[k] Module.Dual k E) :=
    linearMapOperatorSeminorm.comp (dualBaseChangeEquiv k L E).toLinearMap
  apply le_antisymm
  · exact (le_scalarExtensionInjectiveSeminorm_of_ultrametric qd
      (fun a b ↦ by
        change linearMapOperatorSeminorm (dualBaseChangeEquiv k L E (a + b)) ≤ _
        rw [map_add]
        exact linearMapOperatorSeminorm_add_le_max IsUltrametricDist.norm_add_le_max _ _)
      (fun f ↦ by
        change linearMapOperatorSeminorm (dualBaseChangeEquiv k L E ((1 : L) ⊗ₜ[k] f)) ≤
          linearMapOperatorSeminorm f
        rw [dualBaseChangeEquiv_one_tmul]
        exact (scalarExtensionInjective_dualNorm (L := L) f).le)) z
  · apply (scalarExtensionInjectiveSeminorm_le_iff z _).mpr
    intro F
    obtain ⟨x, rfl⟩ := (Module.evalEquiv k E).surjective F
    change ‖scalarExtensionDualEval (Module.Dual.eval k E x) z‖ /
      linearMapOperatorSeminorm (Module.Dual.eval k E x) ≤ _
    rw [scalarExtensionDualEval_eval]
    have h := norm_linearMap_apply_le (dualBaseChangeEquiv k L E z) ((1 : L) ⊗ₜ[k] x)
    have hn : ‖((1 : L) ⊗ₜ[k] x)‖ = linearMapOperatorSeminorm (Module.Dual.eval k E x) :=
      scalarExtensionInjectiveSeminorm_one_tmul_eq_eval_norm (L := L) x
    rw [hn] at h
    by_cases hx : linearMapOperatorSeminorm (Module.Dual.eval k E x) = 0
    · simp only [hx, div_zero]
      exact apply_nonneg _ _
    · exact (div_le_iff₀ (lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hx))).mpr h

end

end ArakelovGeometry

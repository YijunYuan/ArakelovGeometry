/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Duals of completed scalar extensions

The canonical scalar-extension equivalence identifies the completed fibre of the
algebraic dual with the algebraic dual of the completed fibre. Its evaluation
formula fixes the tensor orientation used by norm families. No local norm or
nontriviality assumption on the absolute value is needed.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u v w w'

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
  (E : Type w) [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The canonical equivalence between the scalar extension of the dual and the
dual of the scalar extension, using Mathlib's base-change equivalence. -/
noncomputable def dualBaseChangeEquiv :
    (L ⊗[K] Module.Dual K E) ≃ₗ[L] Module.Dual L (L ⊗[K] E) :=
  (TensorProduct.isBaseChange K E L).toDualBaseChange

@[simp]
theorem dualBaseChangeEquiv_tmul_one (a : L) (ℓ : Module.Dual K E) (x : E) :
    dualBaseChangeEquiv K L E (a ⊗ₜ[K] ℓ) (1 ⊗ₜ[K] x) =
      a * algebraMap K L (ℓ x) :=
  (TensorProduct.isBaseChange K E L).toDualBaseChange_tmul a ℓ x

/-- The pairing defining the canonical equivalence on both pure tensors. -/
@[simp]
theorem dualBaseChangeEquiv_tmul_apply_tmul (a b : L) (ℓ : Module.Dual K E) (x : E) :
    dualBaseChangeEquiv K L E (a ⊗ₜ[K] ℓ) (b ⊗ₜ[K] x) =
      a * b * algebraMap K L (ℓ x) := by
  have h : b ⊗ₜ[K] x = b • ((1 : L) ⊗ₜ[K] x) := by
    simp [TensorProduct.smul_tmul']
  rw [h, map_smul, dualBaseChangeEquiv_tmul_one]
  simp [mul_assoc, mul_left_comm]

/-- The pure-tensor formula agrees with Mathlib's base change of a functional. -/
theorem dualBaseChangeEquiv_tmul (a : L) (ℓ : Module.Dual K E) :
    dualBaseChangeEquiv K L E (a ⊗ₜ[K] ℓ) = a • Module.Dual.baseChange L ℓ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  simp [Algebra.smul_def, mul_assoc, mul_comm]

/-- Multiplication on the completed-field factor becomes scalar multiplication
of the resulting functional. -/
theorem dualBaseChangeEquiv_smul (a : L) (z : L ⊗[K] Module.Dual K E) :
    dualBaseChangeEquiv K L E (a • z) = a • dualBaseChangeEquiv K L E z :=
  map_smul _ _ _

/-- The canonical equivalence intertwines scalar extension of evaluation with
evaluation on the extended space. The dual map supplies the contravariant
identification on the second dual. -/
theorem dualBaseChangeEquiv_eval (z : L ⊗[K] E) :
    dualBaseChangeEquiv K L (Module.Dual K E)
        ((Module.Dual.eval K E).baseChange L z) =
      (dualBaseChangeEquiv K L E).dualMap (Module.Dual.eval L (L ⊗[K] E) z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp [hz, hw]
  | tmul a x =>
    apply TensorProduct.AlgebraTensorModule.ext
    intro b ℓ
    simp [mul_comm]

/-- Equivalently, transporting the scalar extension of evaluation all the way
to the bidual of the extended space gives its usual evaluation map. -/
theorem dualBaseChangeEquiv_eval_symm (z : L ⊗[K] E) :
    (dualBaseChangeEquiv K L E).dualMap.symm
        (dualBaseChangeEquiv K L (Module.Dual K E)
          ((Module.Dual.eval K E).baseChange L z)) =
      Module.Dual.eval L (L ⊗[K] E) z := by
  rw [dualBaseChangeEquiv_eval]
  exact (dualBaseChangeEquiv K L E).dualMap.symm_apply_apply _

/-- The rank-zero case does not need an inhabitant of a basis index type. -/
theorem dualBaseChangeEquiv_eq_zero_of_subsingleton [Subsingleton E]
    (z : L ⊗[K] Module.Dual K E) : dualBaseChangeEquiv K L E z = 0 :=
  Subsingleton.elim _ _

theorem dualBaseChangeEquiv_eq_zero_of_finrank_eq_zero (h : Module.finrank K E = 0)
    (z : L ⊗[K] Module.Dual K E) : dualBaseChangeEquiv K L E z = 0 := by
  let : Subsingleton E := (Module.finrank_eq_zero_iff_of_free K E).mp h
  exact dualBaseChangeEquiv_eq_zero_of_subsingleton K L E z

end ArakelovGeometry

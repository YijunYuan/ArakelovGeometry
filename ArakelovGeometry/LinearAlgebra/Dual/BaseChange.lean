/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Duality under scalar extension

The dual of a finite-dimensional vector space commutes with scalar extension.
We specialize `IsBaseChange.toDualBaseChange` to the tensor product and establish
its pure-tensor formula and compatibility with evaluation into the bidual.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u v w

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
  (E : Type w) [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The tensor-product specialization of `IsBaseChange.toDualBaseChange`. -/
noncomputable abbrev dualBaseChangeEquiv :
    (L ⊗[K] Module.Dual K E) ≃ₗ[L] Module.Dual L (L ⊗[K] E) :=
  (TensorProduct.isBaseChange K E L).toDualBaseChange

/-- The pairing defining the canonical equivalence on both pure tensors. -/
@[simp]
theorem dualBaseChangeEquiv_tmul_apply_tmul (a b : L) (ℓ : Module.Dual K E) (x : E) :
    dualBaseChangeEquiv K L E (a ⊗ₜ[K] ℓ) (b ⊗ₜ[K] x) =
      a * b * algebraMap K L (ℓ x) := by
  have h : b ⊗ₜ[K] x = b • ((1 : L) ⊗ₜ[K] x) := by
    simp [TensorProduct.smul_tmul']
  rw [h, map_smul]
  simpa only [dualBaseChangeEquiv, TensorProduct.mk_apply, smul_eq_mul,
    mul_assoc, mul_left_comm] using
    congrArg (b * ·) ((TensorProduct.isBaseChange K E L).toDualBaseChange_tmul a ℓ x)

/-- The pure-tensor formula agrees with Mathlib's base change of a functional. -/
theorem dualBaseChangeEquiv_tmul (a : L) (ℓ : Module.Dual K E) :
    dualBaseChangeEquiv K L E (a ⊗ₜ[K] ℓ) = a • Module.Dual.baseChange L ℓ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  simp [Algebra.smul_def, mul_assoc, mul_comm]

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

end ArakelovGeometry

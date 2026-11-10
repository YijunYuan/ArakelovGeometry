/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.ScalarExtensionDual

/-!
# Norms under the identity scalar extension

The projective norm on `k ⊗[k] E` is the original norm under the canonical
left-unit equivalence. The injective norm is its bidual supremum, including
trivially valued fields and zero-dimensional spaces.
-/

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable {k E : Type*} [NormedField k] [NormedAddCommGroup E] [NormedSpace k E]

/-- Identity projective extension recovers the original norm, without any
nontriviality or completeness hypothesis on the scalar field. -/
theorem scalarExtensionProjectiveSeminorm_self (z : k ⊗[k] E) :
    scalarExtensionProjectiveSeminorm z = ‖TensorProduct.lid k E z‖ := by
  have hz : (1 : k) ⊗ₜ[k] (TensorProduct.lid k E z) = z := by
    simpa only [TensorProduct.lid_symm_apply] using
      (TensorProduct.lid k E).symm_apply_apply z
  apply le_antisymm
  · conv_lhs => rw [← hz]
    simpa only [norm_one, one_mul] using
      scalarExtensionProjectiveSeminorm_tmul_le (1 : k) (TensorProduct.lid k E z)
  · exact le_scalarExtensionProjectiveSeminorm
      ((normSeminorm k E).comp (TensorProduct.lid k E).toLinearMap)
      (fun x ↦ by simp) z

/-- The rational-vector identity also holds for a specified self-algebra
structure once that structure is proved to be the canonical one. -/
theorem scalarExtensionProjectiveSeminorm_one_tmul_self
    (a : NormedAlgebra k k) (ha : a = NormedAlgebra.id k) (x : E) :
    let := a
    let : Module k k := a.toAlgebra.toModule
    scalarExtensionProjectiveSeminorm ((1 : k) ⊗ₜ[k] x) = ‖x‖ := by
  subst a
  simpa only [TensorProduct.lid_tmul, one_smul] using
    scalarExtensionProjectiveSeminorm_self ((1 : k) ⊗ₜ[k] x)

variable [CompleteSpace k] [FiniteDimensional k E]

/-- Identity injective extension is exactly the bidual supremum under the
canonical left-unit equivalence. -/
theorem scalarExtensionInjectiveSeminorm_self (z : k ⊗[k] E) :
    scalarExtensionInjectiveSeminorm z = sSup (Set.range fun f : E →ₗ[k] k ↦
      ‖f (TensorProduct.lid k E z)‖ / linearMapOperatorSeminorm f) := by
  have hz : (1 : k) ⊗ₜ[k] (TensorProduct.lid k E z) = z := by
    simpa only [TensorProduct.lid_symm_apply] using
      (TensorProduct.lid k E).symm_apply_apply z
  conv_lhs => rw [← hz]
  exact scalarExtensionInjectiveSeminorm_one_tmul _

end

end ArakelovGeometry

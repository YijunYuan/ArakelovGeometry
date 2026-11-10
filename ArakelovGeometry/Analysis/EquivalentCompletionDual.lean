/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DualBaseChange
public import ArakelovGeometry.AdelicVectorBundle.NormFamilyPowerTransport

/-!
# Completed dual pairings under equivalent absolute values

The actual canonical tensor transports intertwine the completed evaluation
pairing through the completed field algebra equivalence.
-/

@[expose] public section

open scoped TensorProduct

namespace AbsoluteValue

variable {K : Type*} [Field K] (v w : AbsoluteValue K ℝ) (h : v.IsEquiv w)
variable (E : Type*) [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Canonical completed tensor transport preserves the actual dual pairing
through the completed field algebra equivalence. -/
theorem completionScalarExtensionEquiv_dualBaseChange_apply
    (z : v.Completion ⊗[K] Module.Dual K E) (y : v.Completion ⊗[K] E) :
    ArakelovGeometry.dualBaseChangeEquiv K w.Completion E
        (completionScalarExtensionEquiv v w h (Module.Dual K E) z)
        (completionScalarExtensionEquiv v w h E y) =
      completionAlgEquivOfIsEquiv v w h
        (ArakelovGeometry.dualBaseChangeEquiv K v.Completion E z y) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [hz, hz']
  | tmul a ℓ =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp [hy, hy']
    | tmul b x =>
      simp only [completionScalarExtensionEquiv_tmul,
        ArakelovGeometry.dualBaseChangeEquiv_tmul_apply_tmul, map_mul,
        AlgEquiv.commutes]

end AbsoluteValue

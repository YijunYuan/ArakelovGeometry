/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Map
public import ArakelovGeometry.Analysis.Determinant.Tensor
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The canonical tensor determinant isomorphism

The basis-independent algebraic producer acts on the existing determinant
lines and finite tensor powers. The final exterior-degree transport is the
accepted equality transport to the actual top exterior power of the tensor.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable (K : Type*) [Field K]
  (E : Type*) [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (F : Type*) [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The product of the two ranks is the rank of the actual tensor space. -/
theorem finrank_mul_eq_tensor :
    Module.finrank K E * Module.finrank K F = Module.finrank K (E ⊗[K] F) :=
  Module.finrank_tensorProduct.symm

/-- The canonical isomorphism from powered determinant lines to the actual
top exterior power of the tensor space. -/
def determinantTensorEquiv :
    ((⨂[K] (_ : Fin (Module.finrank K F)), ⋀[K]^(Module.finrank K E) E) ⊗[K]
      (⨂[K] (_ : Fin (Module.finrank K E)), ⋀[K]^(Module.finrank K F) F)) ≃ₗ[K]
        (⋀[K]^(Module.finrank K (E ⊗[K] F)) (E ⊗[K] F)) :=
  (determinantTensorEquivOfBases (Module.finBasis K E) (Module.finBasis K F)).trans
    (exteriorPowerDegreeEquiv K (E ⊗[K] F) (finrank_mul_eq_tensor K E F))

/-- Every pair of bases gives the same canonical determinant tensor map. -/
theorem determinantTensorEquiv_eq_of_bases
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (c : Module.Basis (Fin (Module.finrank K F)) K F) :
    determinantTensorEquiv K E F = (determinantTensorEquivOfBases b c).trans
      (exteriorPowerDegreeEquiv K (E ⊗[K] F) (finrank_mul_eq_tensor K E F)) := by
  unfold determinantTensorEquiv
  rw [determinantTensorEquivOfBases_eq (Module.finBasis K E) b (Module.finBasis K F) c]

/-- The canonical map sends the two powered wedges to the ordered tensor
wedge. No independence or positivity hypothesis on the tuples is required. -/
theorem determinantTensorEquiv_ιMulti
    (x : Fin (Module.finrank K E) → E) (y : Fin (Module.finrank K F) → F) :
    determinantTensorEquiv K E F
      ((⨂ₜ[K] (_ : Fin (Module.finrank K F)),
        exteriorPower.ιMulti K (Module.finrank K E) x) ⊗ₜ[K]
        (⨂ₜ[K] (_ : Fin (Module.finrank K E)),
          exteriorPower.ιMulti K (Module.finrank K F) y)) =
      exteriorPower.ιMulti K (Module.finrank K (E ⊗[K] F))
        (fun i ↦ x (finProdFinEquiv.symm ((finCongr
            (finrank_mul_eq_tensor K E F)).symm i)).1 ⊗ₜ[K]
          y (finProdFinEquiv.symm ((finCongr
            (finrank_mul_eq_tensor K E F)).symm i)).2) := by
  simp only [determinantTensorEquiv, LinearEquiv.trans_apply,
    determinantTensorEquivOfBases_ιMulti, exteriorPowerDegreeEquiv_ιMulti]

end

end ArakelovGeometry

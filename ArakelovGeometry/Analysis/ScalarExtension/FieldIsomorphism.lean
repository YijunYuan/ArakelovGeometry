/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.ScalarExtension.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

/-!
# Scalar-extension norms under coefficient-field isomorphisms

The canonical tensor equivalence preserves the actual decomposition costs
and extended base-field evaluations, hence both scalar-extension norms.
-/

@[expose] public section

open scoped TensorProduct
namespace ArakelovGeometry
noncomputable section
variable {k L M E : Type*} [NormedField k] [NormedField L] [NormedField M]
  [NormedAlgebra k L] [NormedAlgebra k M] [NormedAddCommGroup E] [NormedSpace k E]

/-- Base-field dual evaluation commutes with canonical coefficient substitution. -/
theorem scalarExtensionDualEval_algEquiv (e : L ≃ₐ[k] M) (f : E →ₗ[k] k)
    (z : L ⊗[k] E) :
    scalarExtensionDualEval f
      (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl k E) z) =
      e (scalarExtensionDualEval f z) := by
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, hz, ht]
  | tmul a x =>
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      scalarExtensionDualEval_tmul, scalarExtensionDualEval_tmul, map_mul, e.commutes]
    rfl

private theorem tensorAlgEquiv_list_sum (e : L ≃ₐ[k] M) (p : List (L × E)) :
    ((p.map fun q ↦ (e q.1, q.2)).map fun q ↦ q.1 ⊗ₜ[k] q.2).sum =
      TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl k E)
        ((p.map fun q ↦ q.1 ⊗ₜ[k] q.2).sum) := by
  induction p with
  | nil => simp only [List.map_nil, List.sum_nil, map_zero]
  | cons q p hp =>
    simp only [List.map_cons, List.sum_cons, map_add, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, hp]
    rfl

omit [NormedSpace k E] in
private theorem scalarExtension_cost_algEquiv (e : L ≃ₐ[k] M)
    (he : ∀ a : L, ‖e a‖ = ‖a‖) (p : List (L × E)) :
    ((p.map fun q ↦ (e q.1, q.2)).map fun q ↦ ‖q.1‖ * ‖q.2‖).sum =
      (p.map fun q ↦ ‖q.1‖ * ‖q.2‖).sum := by
  simp only [List.map_map, Function.comp_def, he]

/-- The full projective decomposition infimum is invariant under an
isometric coefficient-field isomorphism, including the zero space. -/
theorem scalarExtensionProjectiveSeminorm_algEquiv (e : L ≃ₐ[k] M)
    (he : ∀ a : L, ‖e a‖ = ‖a‖) (z : L ⊗[k] E) :
    scalarExtensionProjectiveSeminorm
      (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl k E) z) =
      scalarExtensionProjectiveSeminorm z := by
  have hi (a : M) : ‖e.symm a‖ = ‖a‖ :=
    (he (e.symm a)).symm.trans (congrArg norm (e.apply_symm_apply a))
  have hsymm : TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl k E) =
      (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl k E)).symm := by
    rw [TensorProduct.congr_symm]
    rfl
  rw [scalarExtensionProjectiveSeminorm_eq_sInf, scalarExtensionProjectiveSeminorm_eq_sInf]
  congr 1
  ext c
  constructor
  · rintro ⟨p, hp, hc⟩
    refine ⟨p.map fun q ↦ (e.symm q.1, q.2), ?_, ?_⟩
    · rw [tensorAlgEquiv_list_sum, hp, hsymm, LinearEquiv.symm_apply_apply]
    · exact (scalarExtension_cost_algEquiv e.symm hi p).trans hc
  · rintro ⟨p, hp, hc⟩
    refine ⟨p.map fun q ↦ (e q.1, q.2), ?_, ?_⟩
    · rw [tensorAlgEquiv_list_sum, hp]
    · exact (scalarExtension_cost_algEquiv e he p).trans hc

variable [CompleteSpace k] [FiniteDimensional k E]

/-- Every extended base-functional ratio is unchanged, so the full
injective supremum is invariant under the isometric field isomorphism. -/
theorem scalarExtensionInjectiveSeminorm_algEquiv (e : L ≃ₐ[k] M)
    (he : ∀ a : L, ‖e a‖ = ‖a‖) (z : L ⊗[k] E) :
    scalarExtensionInjectiveSeminorm
      (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl k E) z) =
      scalarExtensionInjectiveSeminorm z := by
  rw [scalarExtensionInjectiveSeminorm_eq_sSup, scalarExtensionInjectiveSeminorm_eq_sSup]
  apply congrArg sSup
  apply congrArg Set.range
  funext f
  rw [scalarExtensionDualEval_algEquiv, he]

end
end ArakelovGeometry

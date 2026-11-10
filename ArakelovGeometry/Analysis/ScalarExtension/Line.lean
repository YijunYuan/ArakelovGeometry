/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.ScalarExtension.Dual
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.EReal.Inv

/-!
# Scalar extension of norms on lines

Both scalar-extension norms and their duals have the exact one-dimensional
formula over arbitrary complete normed fields, including trivial valuations.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable {k E : Type*} [NormedField k] [CompleteSpace k]
  [NormedAddCommGroup E] [NormedSpace k E] [FiniteDimensional k E]

/-- One basis vector computes the operator norm of a functional on a line. -/
theorem linearMapOperatorSeminorm_eq_div_of_basis (b : Module.Basis (Fin 1) k E)
    (f : E →ₗ[k] k) :
    linearMapOperatorSeminorm f = ‖f (b 0)‖ / ‖b 0‖ := by
  have hn : 0 < ‖b 0‖ := norm_pos_iff.mpr (b.ne_zero 0)
  apply le_antisymm
  · apply linearMapOperatorSeminorm_le f (div_nonneg (norm_nonneg _) hn.le)
    intro x
    have hx : (b.repr x) 0 • b 0 = x := by simpa only [Fin.sum_univ_one] using b.sum_repr x
    conv_lhs => rw [← hx, map_smul, norm_smul]
    conv_rhs => rw [← hx, norm_smul]
    apply le_of_eq
    field_simp [hn.ne']
  · exact (div_le_iff₀ hn).mpr (norm_linearMap_apply_le f (b 0))

variable {L : Type*} [NormedField L] [NormedAlgebra k L]

/-- Both extension norms on a line have the scalar-times-generator formula. -/
theorem scalarExtensionSeminorms_tmul_of_basis (b : Module.Basis (Fin 1) k E) (a : L) :
    scalarExtensionProjectiveSeminorm (a ⊗ₜ[k] b 0) = ‖a‖ * ‖b 0‖ ∧
      scalarExtensionInjectiveSeminorm (a ⊗ₜ[k] b 0) = ‖a‖ * ‖b 0‖ := by
  have hc : linearMapOperatorSeminorm (b.coord 0) = ‖b 0‖⁻¹ := by
    rw [linearMapOperatorSeminorm_eq_div_of_basis b]
    simp
  have hε : scalarExtensionInjectiveSeminorm ((1 : L) ⊗ₜ[k] b 0) = ‖b 0‖ := by
    apply le_antisymm (scalarExtensionInjectiveSeminorm_one_tmul_le (b 0))
    have h := scalarExtensionDualRatioSeminorm_le_injective (b.coord 0)
      ((1 : L) ⊗ₜ[k] b 0)
    simpa [scalarExtensionDualRatioSeminorm_apply, hc] using h
  have ht : a ⊗ₜ[k] b 0 = a • ((1 : L) ⊗ₜ[k] b 0) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hεa : scalarExtensionInjectiveSeminorm (a ⊗ₜ[k] b 0) = ‖a‖ * ‖b 0‖ := by
    rw [ht, map_smul_eq_mul, hε]
  refine ⟨le_antisymm (scalarExtensionProjectiveSeminorm_tmul_le a (b 0)) ?_, hεa⟩
  rw [← hεa]
  exact scalarExtensionInjectiveSeminorm_le_projective _

/-- The projective and injective extension norms agree on a line. -/
theorem scalarExtensionProjectiveSeminorm_eq_injective_of_finrank_one
    (hr : Module.finrank k E = 1) (z : L ⊗[k] E) :
    scalarExtensionProjectiveSeminorm z = scalarExtensionInjectiveSeminorm z := by
  let b := Module.finBasisOfFinrankEq k E hr
  let B := b.baseChange L
  have hz : (B.repr z) 0 ⊗ₜ[k] b 0 = z := by
    simpa only [Fin.sum_univ_one, Module.Basis.baseChange_apply,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one, B] using B.sum_repr z
  rw [← hz]
  exact (scalarExtensionSeminorms_tmul_of_basis b _).1.trans
    (scalarExtensionSeminorms_tmul_of_basis b _).2.symm

/-- Projective scalar extension commutes with duality on a line over any
complete valued field extension. -/
theorem scalarExtensionProjective_dual_of_finrank_one [CompleteSpace L]
    (hr : Module.finrank k E = 1) (z : L ⊗[k] Module.Dual k E) :
    let := linearDualNormedAddCommGroup (k := k) (E := E)
    let := linearDualNormedSpace (k := k) (E := E)
    let r := scalarExtensionProjectiveSeminorm (k := k) (L := L) (E := Module.Dual k E)
    let := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
    let := scalarExtensionProjectiveNormedSpace (k := k) (L := L) (E := E)
    linearMapOperatorSeminorm (dualBaseChangeEquiv k L E z) = r z := by
  intro dualGroup dualSpace r extGroup extSpace
  let := dualGroup
  let := dualSpace
  let := extGroup
  let := extSpace
  let b := (Module.finBasisOfFinrankEq k E hr).dualBasis
  let B := b.baseChange L
  let a := (B.repr z) 0
  have hz : a • ((1 : L) ⊗ₜ[k] b 0) = z := by
    simpa only [Fin.sum_univ_one, Module.Basis.baseChange_apply, a, B] using B.sum_repr z
  have hrz : r z = ‖a‖ * linearMapOperatorSeminorm (b 0) := by
    rw [← hz]
    change scalarExtensionProjectiveSeminorm (a • ((1 : L) ⊗ₜ[k] b 0)) = ‖a‖ * ‖b 0‖
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      (scalarExtensionSeminorms_tmul_of_basis b a).1
  rw [hrz, ← hz, map_smul, map_smul_eq_mul, dualBaseChangeEquiv_one_tmul,
    scalarExtensionProjective_dualNorm]

/-- Injective scalar extension commutes with duality on a line over any
complete valued field extension. -/
theorem scalarExtensionInjective_dual_of_finrank_one [CompleteSpace L]
    (hr : Module.finrank k E = 1) (z : L ⊗[k] Module.Dual k E) :
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
  let b := (Module.finBasisOfFinrankEq k E hr).dualBasis
  let B := b.baseChange L
  let a := (B.repr z) 0
  have hz : a • ((1 : L) ⊗ₜ[k] b 0) = z := by
    simpa only [Fin.sum_univ_one, Module.Basis.baseChange_apply, a, B] using B.sum_repr z
  have hrz : r z = ‖a‖ * linearMapOperatorSeminorm (b 0) := by
    rw [← hz]
    change scalarExtensionInjectiveSeminorm (a • ((1 : L) ⊗ₜ[k] b 0)) = ‖a‖ * ‖b 0‖
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      (scalarExtensionSeminorms_tmul_of_basis b a).2
  rw [hrz, ← hz, map_smul, map_smul_eq_mul, dualBaseChangeEquiv_one_tmul,
    scalarExtensionInjective_dualNorm]

end

end ArakelovGeometry

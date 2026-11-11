/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.Tensor.HermitianTensor
public import ArakelovGeometry.Analysis.ScalarExtension.Hermitian.Dual
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-!
# Duality for finite orthogonal tensor products

Canonical algebraic evaluation is isometric on all tensors, with the actual
operator norms on the dual factors. The transport formulation applies directly
to completed fibres through their canonical dual base-change equivalences.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

attribute [-instance] PiTensorProduct.instSeminormedAddCommGroup
  PiTensorProduct.instNormedSpace

variable {L ι : Type*} [RCLike L] [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace L (E i)]
  [∀ i, FiniteDimensional L (E i)]
  {κ : ι → Type*} [∀ i, Fintype (κ i)] (b : ∀ i, OrthonormalBasis (κ i) L (E i))

/-- Canonical finite tensor evaluation preserves the whole orthogonal norm.
The factor equivalences identify existing dual norms; no tensor bound is assumed. -/
theorem orthogonalTensor_dual_transport {A : ι → Type*} {ν : ι → Type*}
    [∀ i, NormedAddCommGroup (A i)] [∀ i, InnerProductSpace L (A i)]
    [∀ i, Fintype (ν i)] (c : ∀ i, OrthonormalBasis (ν i) L (A i))
    (e : ∀ i, A i ≃ₗ[L] Module.Dual L (E i))
    (he : ∀ i x, ‖x‖ = linearMapOperatorSeminorm (e i x)) (z : ⨂[L] i, A i) :
    let := orthogonalTensorNormedAddCommGroup b
    let := orthogonalTensorNormedSpace b
    linearMapOperatorSeminorm (PiTensorProduct.dualDistrib (PiTensorProduct.congr e z)) =
      orthogonalTensorSeminorm c z := by
  classical
  intro nT nsT
  let := nT
  let := nsT
  let := orthogonalTensorInnerProductSpace b
  let c' : ∀ i, OrthonormalBasis (κ i) L (A i) := fun i ↦
    ⟨{ (e i).trans (hermitianDualCoordinates (b i)) with
       norm_map' := fun x ↦ (hermitianDualCoordinates_norm (b i) (e i x)).trans (he i x).symm }⟩
  have heval (t : ⨂[L] i, A i) (p : ∀ i, κ i) :
      orthogonalTensorCoordinates c' t p =
        PiTensorProduct.dualDistrib (PiTensorProduct.congr e t) (⨂ₜ[L] i, b i (p i)) := by
    induction t using PiTensorProduct.induction_on with
    | smul_tprod a x =>
      simp only [map_smul, orthogonalTensorCoordinates_tprod, PiTensorProduct.congr_tprod,
        PiTensorProduct.dualDistrib_apply, LinearMap.smul_apply, smul_eq_mul, PiLp.smul_apply]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact hermitianDualCoordinates_apply (b i) (e i (x i)) (p i)
    | add t u ht hu =>
      simp only [map_add, PiLp.add_apply, LinearMap.add_apply, ht, hu]
  rw [orthogonalTensorSeminorm_eq c c']
  apply (sq_eq_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [linearMapOperatorSeminorm_sq_eq_sum_orthonormal (orthogonalTensorOrthonormalBasis b)]
  change (∑ p, ‖_‖ ^ 2) = ‖orthogonalTensorCoordinates c' z‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro p _
  rw [orthogonalTensorOrthonormalBasis_apply, ← heval]

/-- A formulation in seminorms for transport to actual completed fibres. -/
theorem orthogonalTensor_dual_eq_sSup {A : ι → Type*} {ν : ι → Type*}
    [∀ i, NormedAddCommGroup (A i)] [∀ i, InnerProductSpace L (A i)]
    [∀ i, Fintype (ν i)] (c : ∀ i, OrthonormalBasis (ν i) L (A i))
    (e : ∀ i, A i ≃ₗ[L] Module.Dual L (E i))
    (he : ∀ i x, ‖x‖ = linearMapOperatorSeminorm (e i x)) (z : ⨂[L] i, A i) :
    orthogonalTensorSeminorm c z =
      sSup (Set.range fun t : ⨂[L] i, E i ↦
        ‖PiTensorProduct.dualDistrib (PiTensorProduct.congr e z) t‖ /
          orthogonalTensorSeminorm b t) := by
  let := orthogonalTensorNormedAddCommGroup b
  let := orthogonalTensorNormedSpace b
  exact (orthogonalTensor_dual_transport b c e he z).symm.trans
    (linearMapOperatorSeminorm_eq_sSup _)

end ArakelovGeometry

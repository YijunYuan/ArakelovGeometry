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

omit [∀ i, FiniteDimensional L (E i)] in
/-- Canonical reindexing preserves the orthogonal inner product on all vectors. -/
theorem orthogonalTensorCore_reindex {ι' : Type*} [Fintype ι'] (e : ι ≃ ι')
    (x y : ⨂[L] i, E i) :
    (orthogonalTensorCore (fun j ↦ b (e.symm j))).inner
      (PiTensorProduct.reindex L E e x) (PiTensorProduct.reindex L E e y) =
      (orthogonalTensorCore b).inner x y := by
  classical
  change inner L (orthogonalTensorCoordinates (fun j ↦ b (e.symm j))
    (PiTensorProduct.reindex L E e x))
    (orthogonalTensorCoordinates (fun j ↦ b (e.symm j)) (PiTensorProduct.reindex L E e y)) =
    inner L (orthogonalTensorCoordinates b x) (orthogonalTensorCoordinates b y)
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s y =>
      simp only [map_smul, PiTensorProduct.reindex_tprod, inner_smul_left, inner_smul_right]
      change s * ((starRingEnd L) r * (orthogonalTensorCore (fun j ↦ b (e.symm j))).inner _ _) =
        s * ((starRingEnd L) r * (orthogonalTensorCore b).inner _ _)
      rw [orthogonalTensorCore_tprod, orthogonalTensorCore_tprod]
      congr 2
      exact Fintype.prod_equiv e.symm _ _ (fun _ ↦ rfl)
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]

omit [∀ i, FiniteDimensional L (E i)] in
/-- Every canonical finite permutation is an isometry for the orthogonal norm. -/
theorem orthogonalTensorSeminorm_reindex {ι' : Type*} [Fintype ι'] (e : ι ≃ ι')
    (z : ⨂[L] i, E i) :
    orthogonalTensorSeminorm (fun j ↦ b (e.symm j)) (PiTensorProduct.reindex L E e z) =
      orthogonalTensorSeminorm b z := by
  apply (sq_eq_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [orthogonalTensorSeminorm_sq, orthogonalTensorSeminorm_sq, orthogonalTensorCore_reindex]

section InjectiveReindex

variable {k I J : Type*} [NormedField k] [CompleteSpace k] [Fintype I] [Fintype J]
  {V : I → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace k (V i)]
  [∀ i, FiniteDimensional k (V i)]

omit [CompleteSpace k] [∀ i, FiniteDimensional k (V i)] in
/-- Reindexing respects the algebraic evaluation pairing on arbitrary tensors. -/
theorem tensorDualEval_reindex (e : I ≃ J) (φ : ∀ i, Module.Dual k (V i))
    (z : ⨂[k] i, V i) :
    tensorDualEval (fun j ↦ φ (e.symm j)) (PiTensorProduct.reindex k V e z) =
      tensorDualEval φ z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    simp only [map_smul, PiTensorProduct.reindex_tprod, tensorDualEval_tprod]
    congr 1
    exact Fintype.prod_equiv e.symm _ _ (fun _ ↦ rfl)
  | add z t hz ht => simp only [map_add, hz, ht]

/-- Reindexing preserves the injective norm over any complete normed field. -/
theorem injectiveTensorSeminorm_reindex (e : I ≃ J) (z : ⨂[k] i, V i) :
    injectiveTensorSeminorm (PiTensorProduct.reindex k V e z) = injectiveTensorSeminorm z := by
  rw [injectiveTensorSeminorm_eq_sSup, injectiveTensorSeminorm_eq_sSup]
  congr 1
  rw [← (Equiv.piCongrLeft' (fun i ↦ Module.Dual k (V i)) e).surjective.range_comp]
  congr 1
  funext φ
  change ‖tensorDualEval (fun j ↦ φ (e.symm j)) (PiTensorProduct.reindex k V e z)‖ /
    (∏ j, linearMapOperatorSeminorm (φ (e.symm j))) = _
  rw [tensorDualEval_reindex]
  congr 1
  exact Fintype.prod_equiv e.symm _ _ (fun _ ↦ rfl)

end InjectiveReindex

end ArakelovGeometry

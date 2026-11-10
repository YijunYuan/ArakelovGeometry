/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.ArchimedeanDual
public import ArakelovGeometry.Analysis.DeterminantNorm
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Bounds for determinant pairings

These estimates control the actual exterior-dual evaluation under the
projective determinant quotient. The non-Archimedean estimate allows arbitrary
vector norms; the Archimedean estimate uses the given inner product.
-/

@[expose] public section

namespace ArakelovGeometry

noncomputable section

section InnerProduct

variable {L E : Type*} [RCLike L] [NormedAddCommGroup E]
  [InnerProductSpace L E] [FiniteDimensional L E] {n : ℕ}

/-- Hadamard's inequality in an orthonormal basis over the real or complex field. -/
theorem norm_orthonormalBasis_det_le (b : OrthonormalBasis (Fin n) L E)
    (x : Fin n → E) : ‖b.toBasis.det x‖ ≤ ∏ i, ‖x i‖ := by
  classical
  have hd : Module.finrank L E = Fintype.card (Fin n) :=
    Module.finrank_eq_card_basis b.toBasis
  let c := InnerProductSpace.gramSchmidtOrthonormalBasis hd x
  rw [b.toBasis.det.eq_smul_basis_det c.toBasis, smul_apply,
    norm_smul, OrthonormalBasis.coe_toBasis, b.det_to_matrix_orthonormalBasis c, one_mul]
  rw [InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  apply Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _)
  intro i _
  simpa only [c.orthonormal.1 i, one_mul] using
    norm_inner_le_norm (c i) (x i)

/-- Dual evaluation on an orthonormal basis satisfies the dual Hadamard bound. -/
theorem norm_det_dual_orthonormalBasis_le (b : OrthonormalBasis (Fin n) L E)
    (f : Fin n → E →ₗ[L] L) :
    ‖(Matrix.of fun i j ↦ f j (b i)).det‖ ≤
      ∏ i, linearMapOperatorSeminorm (f i) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete L E
  let y (i : Fin n) := (InnerProductSpace.toDual L E).symm
    (LinearMap.toContinuousLinearMap (f i))
  have hy (i : Fin n) : ‖y i‖ = linearMapOperatorSeminorm (f i) := by
    rw [show ‖y i‖ = ‖LinearMap.toContinuousLinearMap (f i)‖ from
      (InnerProductSpace.toDual L E).symm.norm_map _]
    exact (linearMapOperatorSeminorm_coe_continuousLinearMap
      (LinearMap.toContinuousLinearMap (f i))).symm
  have hm : (Matrix.of fun i j ↦ f j (b i)) =
      (b.toBasis.toMatrix y).map (starRingEnd L) := by
    ext i j
    change f j (b i) = star (b.toBasis.repr (y j) i)
    rw [b.coe_toBasis_repr_apply, b.repr_apply_apply, ← inner_conj_symm]
    simp [y]
  have hdet := (starRingEnd L).map_det (b.toBasis.toMatrix y)
  change star (b.toBasis.toMatrix y).det =
    ((b.toBasis.toMatrix y).map (starRingEnd L)).det at hdet
  rw [hm, ← hdet]
  change ‖star (b.toBasis.det y)‖ ≤ _
  rw [norm_star]
  simpa only [hy] using norm_orthonormalBasis_det_le b y

/-- The determinant of dual evaluation is bounded by the two products of norms
on an inner-product space. -/
theorem norm_det_pairing_le_of_innerProduct (f : Fin n → E →ₗ[L] L)
    (x : Fin n → E) (hd : Module.finrank L E = n) :
    ‖(Matrix.of fun i j ↦ f j (x i)).det‖ ≤
      (∏ i, ‖x i‖) * ∏ i, linearMapOperatorSeminorm (f i) := by
  classical
  let b := (stdOrthonormalBasis L E).reindex (finCongr hd)
  let F := (_root_.exteriorPower.pairingDual L E n
    (_root_.exteriorPower.ιMulti L n f)).compAlternatingMap
      (_root_.exteriorPower.ιMulti L n)
  have hf : (Matrix.of fun i j ↦ f j (x i)).det =
      (Matrix.of fun i j ↦ f j (b i)).det * b.toBasis.det x := by
    have h := congrArg (fun g ↦ g x) (F.eq_smul_basis_det b.toBasis)
    simpa only [F, LinearMap.compAlternatingMap_apply,
      _root_.exteriorPower.pairingDual_ιMulti_ιMulti, smul_apply,
      OrthonormalBasis.coe_toBasis, smul_eq_mul] using h
  rw [hf, norm_mul]
  exact (mul_le_mul (norm_det_dual_orthonormalBasis_le b f)
    (norm_orthonormalBasis_det_le b x) (norm_nonneg _)
      (Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _)).trans_eq (mul_comm _ _)

end InnerProduct

section Ultrametric

variable {L : Type*} [NormedField L] [IsUltrametricDist L]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A non-Archimedean determinant obeys a row-column product bound, with
no factorial factor. Empty matrices and zero weights are included. -/
theorem norm_det_le_prod_of_entry_le (M : Matrix ι ι L) (a b : ι → ℝ)
    (hM : ∀ i j, ‖M i j‖ ≤ a i * b j) :
    ‖M.det‖ ≤ (∏ i, a i) * ∏ i, b i := by
  rw [Matrix.det_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty Finset.univ_nonempty
  intro σ _
  rw [norm_units_zsmul, norm_prod]
  calc
    ∏ i, ‖M (σ i) i‖ ≤ ∏ i, a (σ i) * b i :=
      Finset.prod_le_prod₀ (fun i _ ↦ norm_nonneg _) (fun i _ ↦ hM (σ i) i)
    _ = (∏ i, a i) * ∏ i, b i := by
      rw [Finset.prod_mul_distrib, Equiv.prod_comp σ]

/-- Evaluation of dual wedges has the product bound over every complete
non-Archimedean field, even when the vector norm is not ultrametric. -/
theorem norm_det_pairing_le_of_ultrametric [CompleteSpace L]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace L E] [FiniteDimensional L E]
    (f : ι → E →ₗ[L] L) (x : ι → E) :
    ‖(Matrix.of fun i j ↦ f j (x i)).det‖ ≤
      (∏ i, ‖x i‖) * ∏ i, linearMapOperatorSeminorm (f i) := by
  apply norm_det_le_prod_of_entry_le _ (fun i ↦ ‖x i‖)
    (fun i ↦ linearMapOperatorSeminorm (f i))
  intro i j
  simpa only [Matrix.of_apply, mul_comm] using norm_linearMap_apply_le (f j) (x i)

end Ultrametric

end

end ArakelovGeometry

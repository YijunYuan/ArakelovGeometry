/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.ArchimedeanDual
public import ArakelovGeometry.Analysis.TensorNorm
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Hermitian norms on finite tensor products

The actual finite tensor product is given the inner product whose values on
pure tensors are products of the factor inner products. Orthonormal bases
construct the positive definite form through its Euclidean coordinates;
the pure-tensor identity proves that the form is independent of those bases.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

variable {L ι : Type*} [RCLike L] [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace L (E i)]
  {κ : ι → Type*} [∀ i, Fintype (κ i)] (b : ∀ i, OrthonormalBasis (κ i) L (E i))

/-- Euclidean coordinates of the actual tensor-product basis. -/
def orthogonalTensorCoordinates : (⨂[L] i, E i) ≃ₗ[L] EuclideanSpace L (∀ i, κ i) :=
  (Basis.piTensorProduct (fun i => (b i).toBasis)).equivFun.trans
    (WithLp.linearEquiv 2 L ((∀ i, κ i) → L)).symm

/-- A pure tensor has the product of the factor coordinates. -/
theorem orthogonalTensorCoordinates_tprod (x : ∀ i, E i) (j : ∀ i, κ i) :
    orthogonalTensorCoordinates b (⨂ₜ[L] i, x i) j = ∏ i, (b i).repr (x i) (j i) := by
  change (Basis.piTensorProduct (fun i => (b i).toBasis)).equivFun _ j = _
  simp only [Module.Basis.equivFun_apply, Basis.piTensorProduct_repr_tprod_apply,
    OrthonormalBasis.coe_toBasis_repr_apply]

/-- The Euclidean coordinate norm as a seminorm on the original tensor product. -/
def orthogonalTensorSeminorm : Seminorm L (⨂[L] i, E i) := by
  classical
  exact (normSeminorm L (EuclideanSpace L (∀ i, κ i))).comp
    (orthogonalTensorCoordinates b).toLinearMap

/-- The orthogonal seminorm separates zero, even with a zero-dimensional factor. -/
theorem orthogonalTensorSeminorm_eq_zero_iff (z : ⨂[L] i, E i) :
    orthogonalTensorSeminorm b z = 0 ↔ z = 0 := by
  classical
  change ‖orthogonalTensorCoordinates b z‖ = 0 ↔ _
  rw [norm_eq_zero, LinearEquiv.map_eq_zero_iff]

/-- The coordinate inner product is positive definite on the existing tensor module. -/
@[instance_reducible]
def orthogonalTensorCore : InnerProductSpace.Core L (⨂[L] i, E i) := by
  classical
  exact
    { inner x y := inner L (orthogonalTensorCoordinates b x) (orthogonalTensorCoordinates b y)
      conj_inner_symm _ _ := inner_conj_symm _ _
      re_inner_nonneg _ := inner_self_nonneg
      add_left x y z := by simp only [map_add, inner_add_left]
      smul_left x y a := by simp only [map_smul, inner_smul_left]
      definite x h := (orthogonalTensorCoordinates b).map_eq_zero_iff.mp (inner_self_eq_zero.mp h) }

/-- The defining product formula on pure tensors, in Mathlib's convention
that the first inner-product variable is conjugate-linear. -/
theorem orthogonalTensorCore_tprod (x y : ∀ i, E i) :
    (orthogonalTensorCore b).inner (⨂ₜ[L] i, x i) (⨂ₜ[L] i, y i) =
      ∏ i, inner L (x i) (y i) := by
  classical
  change inner L (orthogonalTensorCoordinates b _) (orthogonalTensorCoordinates b _) = _
  rw [PiLp.inner_apply]
  simp only [orthogonalTensorCoordinates_tprod, RCLike.inner_apply, map_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i j => (b i).repr (y i) j * (starRingEnd L) ((b i).repr (x i) j))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← (b i).repr.inner_map_map (x i) (y i), PiLp.inner_apply]
  rfl

/-- The core induces exactly the prescribed orthogonal tensor seminorm. -/
theorem orthogonalTensorSeminorm_sq (z : ⨂[L] i, E i) :
    (orthogonalTensorSeminorm b z) ^ 2 = RCLike.re ((orthogonalTensorCore b).inner z z) := by
  classical
  exact norm_sq_eq_re_inner (𝕜 := L) (orthogonalTensorCoordinates b z)

/-- The orthogonal norm of a pure tensor is the product of all factor norms,
including the empty tensor product. -/
theorem orthogonalTensorSeminorm_tprod (x : ∀ i, E i) :
    orthogonalTensorSeminorm b (⨂ₜ[L] i, x i) = ∏ i, ‖x i‖ := by
  apply (sq_eq_sq₀ (apply_nonneg _ _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)).mp
  rw [orthogonalTensorSeminorm_sq, orthogonalTensorCore_tprod]
  simp only [inner_self_eq_norm_sq_to_K, ← map_pow, ← map_prod, RCLike.ofReal_re,
    Finset.prod_pow]

/-- The inner product is independent of the orthonormal bases: pure tensors
span each variable, so their product formula determines the whole form. -/
theorem orthogonalTensorCore_inner_eq {κ' : ι → Type*} [∀ i, Fintype (κ' i)]
    (b' : ∀ i, OrthonormalBasis (κ' i) L (E i)) (x y : ⨂[L] i, E i) :
    (orthogonalTensorCore b).inner x y = (orthogonalTensorCore b').inner x y := by
  classical
  change inner L (orthogonalTensorCoordinates b x) (orthogonalTensorCoordinates b y) =
    inner L (orthogonalTensorCoordinates b' x) (orthogonalTensorCoordinates b' y)
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod s y =>
          simp only [map_smul, inner_smul_left, inner_smul_right]
          change s * ((starRingEnd L) r * (orthogonalTensorCore b).inner _ _) =
            s * ((starRingEnd L) r * (orthogonalTensorCore b').inner _ _)
          rw [orthogonalTensorCore_tprod, orthogonalTensorCore_tprod]
      | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]

/-- Consequently the orthogonal norm itself is independent of the basis choice. -/
theorem orthogonalTensorSeminorm_eq {κ' : ι → Type*} [∀ i, Fintype (κ' i)]
    (b' : ∀ i, OrthonormalBasis (κ' i) L (E i)) :
    orthogonalTensorSeminorm b = orthogonalTensorSeminorm b' := by
  ext z
  apply (sq_eq_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [orthogonalTensorSeminorm_sq, orthogonalTensorSeminorm_sq,
    orthogonalTensorCore_inner_eq b b' z z]

/-- The orthogonal tensor norm is bounded by the projective norm through
the genuine projective universal inequality and the pure-tensor norm identity. -/
theorem orthogonalTensorSeminorm_le_projective :
    orthogonalTensorSeminorm b ≤ PiTensorProduct.projectiveSeminorm := by
  classical
  intro z
  simpa only [one_mul, orthogonalTensorSeminorm, Seminorm.comp_apply, coe_normSeminorm,
    LinearEquiv.coe_coe] using
    norm_linearMap_le_projective_of_tprod_le (orthogonalTensorCoordinates b).toLinearMap
      zero_le_one (fun x => by
        simpa only [one_mul, orthogonalTensorSeminorm, Seminorm.comp_apply, coe_normSeminorm,
          LinearEquiv.coe_coe] using (orthogonalTensorSeminorm_tprod b x).le) z

variable [∀ i, FiniteDimensional L (E i)]

/-- Product dual evaluations are bounded by the orthogonal norm. The Riesz
vectors form a pure tensor, whose norm is the product of the actual dual norms. -/
theorem norm_tensorDualEval_le_orthogonal (φ : ∀ i, E i →ₗ[L] L) (z : ⨂[L] i, E i) :
    ‖tensorDualEval φ z‖ ≤
      (∏ i, linearMapOperatorSeminorm (φ i)) * orthogonalTensorSeminorm b z := by
  classical
  let : ∀ i, CompleteSpace (E i) := fun i => FiniteDimensional.complete L (E i)
  let y : ∀ i, E i := fun i =>
    (InnerProductSpace.toDual L (E i)).symm (LinearMap.toContinuousLinearMap (φ i))
  have hy (i : ι) : ‖y i‖ = linearMapOperatorSeminorm (φ i) := by
    dsimp only [y]
    rw [LinearIsometryEquiv.norm_map]
    exact (linearMapOperatorSeminorm_coe_continuousLinearMap
      (LinearMap.toContinuousLinearMap (φ i))).symm
  have he : tensorDualEval φ =
      ((innerSL L (orthogonalTensorCoordinates b (⨂ₜ[L] i, y i))).toLinearMap.comp
        (orthogonalTensorCoordinates b).toLinearMap) := by
    apply PiTensorProduct.ext
    ext x
    change tensorDualEval φ (⨂ₜ[L] i, x i) =
      (orthogonalTensorCore b).inner (⨂ₜ[L] i, y i) (⨂ₜ[L] i, x i)
    rw [tensorDualEval_tprod, orthogonalTensorCore_tprod]
    apply Finset.prod_congr rfl
    intro i hi
    exact (InnerProductSpace.toDual_symm_apply (x := x i)
      (y := LinearMap.toContinuousLinearMap (φ i))).symm
  rw [he]
  change ‖inner L (orthogonalTensorCoordinates b (⨂ₜ[L] i, y i))
    (orthogonalTensorCoordinates b z)‖ ≤ _
  calc
    _ ≤ ‖orthogonalTensorCoordinates b (⨂ₜ[L] i, y i)‖ *
        ‖orthogonalTensorCoordinates b z‖ := norm_inner_le_norm _ _
    _ = (∏ i, linearMapOperatorSeminorm (φ i)) * orthogonalTensorSeminorm b z := by
      change orthogonalTensorSeminorm b (⨂ₜ[L] i, y i) * orthogonalTensorSeminorm b z = _
      rw [orthogonalTensorSeminorm_tprod]
      simp only [hy]

/-- The genuine injective tensor norm is bounded by the orthogonal tensor norm. -/
theorem injectiveTensorSeminorm_le_orthogonal :
    injectiveTensorSeminorm ≤ orthogonalTensorSeminorm b := by
  intro z
  apply (injectiveTensorSeminorm_le_iff z _).mpr
  intro φ
  by_cases hD : ∏ i, linearMapOperatorSeminorm (φ i) = 0
  · simp only [hD, div_zero]
    exact apply_nonneg _ _
  have hpos : 0 < ∏ i, linearMapOperatorSeminorm (φ i) :=
    lt_of_le_of_ne (Finset.prod_nonneg fun _ _ => apply_nonneg _ _) (Ne.symm hD)
  apply (div_le_iff₀ hpos).mpr
  simpa only [mul_comm] using norm_tensorDualEval_le_orthogonal b φ z

/-- The empty orthogonal tensor product has exactly the norm of the unit field. -/
theorem orthogonalTensorSeminorm_isEmpty [IsEmpty ι] (z : ⨂[L] i, E i) :
    orthogonalTensorSeminorm b z = ‖PiTensorProduct.isEmptyEquiv ι z‖ :=
  le_antisymm ((orthogonalTensorSeminorm_le_projective b z).trans_eq (projectiveSeminorm_isEmpty z))
    ((injectiveTensorSeminorm_isEmpty z).symm.le.trans (injectiveTensorSeminorm_le_orthogonal b z))

end ArakelovGeometry

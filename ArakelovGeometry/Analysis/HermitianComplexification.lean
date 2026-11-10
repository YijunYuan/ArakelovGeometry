/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.HermitianScalarExtensionTensor

/-!
# The corrected uniqueness criterion for Hermitian complexification

Restriction of a Hermitian norm to the original real space does not determine
the extended Hermitian form. Conjugation invariance is the missing condition.
-/

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Canonical conjugation acts only on the complex scalar factor. -/
def complexificationConj : (ℂ ⊗[ℝ] E) ≃ₗ[ℝ] (ℂ ⊗[ℝ] E) :=
  TensorProduct.congr Complex.conjLIE.toLinearEquiv (LinearEquiv.refl ℝ E)

@[simp]
theorem complexificationConj_tmul (a : ℂ) (x : E) :
    complexificationConj (a ⊗ₜ[ℝ] x) = (starRingEnd ℂ a) ⊗ₜ[ℝ] x := rfl

section Normed

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι]
  (b : OrthonormalBasis ι ℝ V)

/-- The canonical Hermitian complexification is invariant under
canonical conjugation, in every finite dimension including zero. -/
theorem hermitianScalarExtensionSeminorm_conj (z : ℂ ⊗[ℝ] V) :
    hermitianScalarExtensionSeminorm b (complexificationConj z) =
      hermitianScalarExtensionSeminorm b z := by
  let := normedAlgebraInnerProductSpace (k := ℝ) (L := ℂ)
  rw [hermitianScalarExtensionSeminorm_eq_tensor_norm,
    hermitianScalarExtensionSeminorm_eq_tensor_norm]
  exact (TensorProduct.congrIsometry Complex.conjLIE
    (LinearIsometryEquiv.refl ℝ V)).norm_map z

omit [Fintype ι] in
/-- Restriction of the norm and conjugation invariance force the entire
Hermitian pairing on original real vectors, not just its real part. -/
theorem complexificationCore_inner_of_conj
    (c : InnerProductSpace.Core ℂ (ℂ ⊗[ℝ] V))
    (hres : ∀ x : V,
      Real.sqrt (c.inner ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] x)).re = ‖x‖)
    (hc : ∀ z : ℂ ⊗[ℝ] V,
      Real.sqrt (c.inner (complexificationConj z) (complexificationConj z)).re =
        Real.sqrt (c.inner z z).re) (x y : V) :
    c.inner ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y) = (inner ℝ x y : ℂ) := by
  let := c
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ℂ ⊗[ℝ] V)
  let := InnerProductSpace.ofCore c.toCore
  change ∀ x : V, ‖(1 : ℂ) ⊗ₜ[ℝ] x‖ = ‖x‖ at hres
  change ∀ z : ℂ ⊗[ℝ] V, ‖complexificationConj z‖ = ‖z‖ at hc
  change inner ℂ ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y) = (inner ℝ x y : ℂ)
  apply Complex.ext
  · change (inner ℂ ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y)).re = inner ℝ x y
    have hr := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
      (𝕜 := ℂ) ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y)
    rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_sub, hres, hres] at hr
    exact hr.trans
      (re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℝ) x y).symm
  · have heq : ‖(1 : ℂ) ⊗ₜ[ℝ] x - Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] y)‖ =
        ‖(1 : ℂ) ⊗ₜ[ℝ] x + Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] y)‖ := by
      simpa only [map_add, complexificationConj_tmul, map_one, Complex.conj_I,
        TensorProduct.neg_tmul, sub_eq_add_neg, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one] using hc ((1 : ℂ) ⊗ₜ[ℝ] x + Complex.I ⊗ₜ[ℝ] y)
    have hi := complexEmbedding_inner_im (RingHom.id ℂ) (fun _ ↦ rfl) Complex.I rfl
      ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y)
    simpa only [RingHom.id_apply, heq, sub_self, zero_div, Complex.ofReal_im] using hi

/-- Extension of the real inner product as a pairing uniquely determines
the Hermitian form on the actual complex scalar extension. -/
theorem complexificationCore_inner_eq_of_restrict
    (c : InnerProductSpace.Core ℂ (ℂ ⊗[ℝ] V))
    (hc : ∀ x y : V, c.inner ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y) =
      (inner ℝ x y : ℂ)) (z t : ℂ ⊗[ℝ] V) :
    c.inner z t = (hermitianScalarExtensionCore b).inner z t := by
  let d := hermitianScalarExtensionCore (L := ℂ) b
  change c.inner z t = d.inner z t
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [InnerProductSpace.Core.inner_zero_left (c := c.toCore),
      InnerProductSpace.Core.inner_zero_left (c := d.toCore)]
  | add z u hz hu =>
    simp only [InnerProductSpace.Core.inner_add_left (c := c.toCore),
      InnerProductSpace.Core.inner_add_left (c := d.toCore), hz, hu]
  | tmul a x =>
    induction t using TensorProduct.induction_on with
    | zero =>
      simp only [InnerProductSpace.Core.inner_zero_right (c := c.toCore),
        InnerProductSpace.Core.inner_zero_right (c := d.toCore)]
    | add t u ht hu =>
      simp only [InnerProductSpace.Core.inner_add_right (c := c.toCore),
        InnerProductSpace.Core.inner_add_right (c := d.toCore), ht, hu]
    | tmul e y =>
      calc
        c.inner (a ⊗ₜ[ℝ] x) (e ⊗ₜ[ℝ] y) =
            starRingEnd ℂ a * e * (inner ℝ x y : ℂ) := by
          rw [show a ⊗ₜ[ℝ] x = a • ((1 : ℂ) ⊗ₜ[ℝ] x) by
            simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
          rw [show e ⊗ₜ[ℝ] y = e • ((1 : ℂ) ⊗ₜ[ℝ] y) by
            simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
          rw [InnerProductSpace.Core.inner_smul_left (c := c.toCore),
            InnerProductSpace.Core.inner_smul_right (c := c.toCore), hc]
          ring
        _ = d.inner (a ⊗ₜ[ℝ] x) (e ⊗ₜ[ℝ] y) :=
          (hermitianScalarExtensionCore_tmul b a e x y).symm

/-- A Hermitian norm extending a real norm is its canonical Hermitian
complexification exactly when it is invariant under canonical conjugation.
The square roots are the norms induced by the positive definite core `c`. -/
theorem hermitianComplexification_conjugation_criterion
    (c : InnerProductSpace.Core ℂ (ℂ ⊗[ℝ] V))
    (hres : ∀ x : V,
      Real.sqrt (c.inner ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] x)).re = ‖x‖) :
    (∀ z : ℂ ⊗[ℝ] V,
      Real.sqrt (c.inner z z).re = hermitianScalarExtensionSeminorm b z) ↔
    (∀ z : ℂ ⊗[ℝ] V,
      Real.sqrt (c.inner (complexificationConj z) (complexificationConj z)).re =
        Real.sqrt (c.inner z z).re) := by
  constructor
  · intro h z
    rw [h, h]
    exact hermitianScalarExtensionSeminorm_conj b z
  · intro hc z
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (apply_nonneg _ _)).mp
    calc
      (Real.sqrt (c.inner z z).re) ^ 2 = (c.inner z z).re :=
        Real.sq_sqrt (c.re_inner_nonneg z)
      _ = ((hermitianScalarExtensionCore b).inner z z).re :=
        congrArg Complex.re (complexificationCore_inner_eq_of_restrict b c
          (complexificationCore_inner_of_conj c hres hc) z z)
      _ = (hermitianScalarExtensionSeminorm b z) ^ 2 :=
        (hermitianScalarExtensionSeminorm_sq b z).symm

end Normed

end ArakelovGeometry

end

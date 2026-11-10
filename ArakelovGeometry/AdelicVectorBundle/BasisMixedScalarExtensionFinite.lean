/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDomination

/-!
# Finite-place scalar extension of mixed basis norms

The ordinary injective extension of the mixed coordinate family equals the
coordinate maximum on every extended completed vector, including rank zero.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι K E)

/-- All completed vectors have exactly the mixed extended-basis norm at a
finite place; no nonzero-rank assumption is needed. -/
theorem ofBasisMixed_scalarExtension_norm_of_finite
    (x : S.ParameterSpaceExtension L) (hx : x.base ∈ S.Ωfin)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    ((ofBasisMixed S E b).scalarExtension (L := L)).norm x z =
      (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x z := by
  classical
  apply le_antisymm
  · have h := scalarExtension_norm_le_mul_of_basis_norm_le (ofBasisMixed S E b)
      b x (show (0 : ℝ) ≤ 1 by norm_num) (fun i => ?_) z
    · simpa only [one_mul] using h
    · simp only [Module.Basis.baseChange_apply, ofBasisMixed_norm_tmul_basis, norm_one, le_refl]
  · erw [ofBasisMixed_norm_of_finite (S := S.algebraicExtension L) (b.baseChange L) x
      ((scalarExtension_mem_Ωfin_iff x).mpr hx)]
    have h := ofBasis_norm_le_mul_scalarExtension_of_dual_basis_norm_le
      (ofBasisMixed S E b) b x (show (0 : ℝ) ≤ 1 by norm_num) (fun i => ?_) z
    · simpa only [one_mul] using h
    · simp only [ofBasisMixed_dual, ofBasis_norm_tmul_basis, norm_one, le_refl]

end ArakelovGeometry.NormFamily

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.BasisDomination
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basis.Finite
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Mixed coordinate norms commute with algebraic scalar extension

At infinite places the projective extension is exactly the coordinate sum.
Together with the finite-place coordinate maximum, this proves Example 4.1.5
on every actual extended completed vector, with the empty basis included.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

universe u w wE

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι K E)

/-- The transported mixed coordinate seminorm is below the actual projective
extension on every vector of the extended completed fibre. -/
theorem ofBasisMixed_norm_le_projectiveScalarExtension_norm
    (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x z ≤
      ((ofBasisMixed S E b).projectiveScalarExtension (L := L)).norm x z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let ξ := ofBasisMixed S E b
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let e := completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
  let q : Seminorm x.abv.Completion (x.abv.Completion ⊗[L] (L ⊗[K] E)) :=
    (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x
  let p : Seminorm x.abv.Completion
      (x.abv.Completion ⊗[(S.ϕ x.base).Completion] ((S.ϕ x.base).Completion ⊗[K] E)) :=
    q.comp e.symm.toLinearMap
  have hp : p ≤ scalarExtensionProjectiveSeminorm := by
    apply le_scalarExtensionProjectiveSeminorm
    intro y
    change (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x
      (e.symm ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] y)) ≤ ξ.norm x.base y
    exact (ofBasisMixed_norm_chosenExtensionMap b x.base x.abv x.restrict_eq y).le
  have h := hp (e z)
  change q (e.symm (e z)) ≤ scalarExtensionProjectiveSeminorm (e z) at h
  rw [e.symm_apply_apply] at h
  exact h

/-- At infinite places the projective branch equals the mixed extended-basis
family on every completed vector. -/
theorem ofBasisMixed_scalarExtension_norm_of_infinite
    (x : S.ParameterSpaceExtension L) (hx : x.base ∈ S.Ωinf)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    ((ofBasisMixed S E b).scalarExtension (L := L)).norm x z =
      (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x z := by
  apply le_antisymm
  · have h := scalarExtension_norm_le_mul_of_basis_norm_le (ofBasisMixed S E b)
      b x (show (0 : ℝ) ≤ 1 by norm_num) (fun i => ?_) z
    · simpa only [one_mul] using h
    · simp only [Module.Basis.baseChange_apply, ofBasisMixed_norm_tmul_basis, norm_one, le_refl]
  · rw [scalarExtension_norm_of_not_mem_Ωfin _ x hx]
    exact ofBasisMixed_norm_le_projectiveScalarExtension_norm b x z

/-- Source Example 4.1.5: ordinary algebraic scalar extension of the mixed
basis family is exactly the mixed family of the extended basis, in all ranks. -/
theorem ofBasisMixed_scalarExtension :
    (ofBasisMixed S E b).scalarExtension (L := L) =
      ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L) := by
  ext x z
  change S.ParameterSpaceExtension L at x
  change x.abv.Completion ⊗[L] (L ⊗[K] E) at z
  by_cases hx : x.base ∈ S.Ωfin
  · exact ofBasisMixed_scalarExtension_norm_of_finite b x hx z
  · exact ofBasisMixed_scalarExtension_norm_of_infinite b x hx z

end ArakelovGeometry.NormFamily

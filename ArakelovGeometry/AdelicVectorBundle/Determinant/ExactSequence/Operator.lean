/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.ExactSequence
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Pair
import ArakelovGeometry.AdelicVectorBundle.Determinant.ExactSequence.Norm
import ArakelovGeometry.AdelicVectorBundle.Operator.LineHeight
import ArakelovGeometry.AdelicVectorBundle.Tensor.Line
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Operator contraction of the canonical exact-sequence determinant map

The domain carries the existing binary injective tensor norm on its two
actual determinant lines. Its rational generator product formula identifies
this norm with the source tensor-line norm in every rank.
-/

@[expose] public section

open scoped TensorProduct

universe w w'

namespace ArakelovGeometry.NormFamily

noncomputable section

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The existing binary tensor norm has the product value on nonzero
rational generators of two lines. -/
theorem injectiveTensorPair_norm_rational_generators
    (ξ : NormFamily S E) (η : NormFamily S F)
    (hE : Module.finrank K E = 1) (hF : Module.finrank K F = 1)
    {x : E} {y : F} (hx : x ≠ 0) (hy : y ≠ 0) (ω : S.Ω) :
    (ξ.injectiveTensorPair η).norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (x ⊗ₜ[K] y)) =
      ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) *
        η.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] y) := by
  let v : ∀ i, LiftedTensorFactors E F i := fun i ↦ match i with
    | .inl _ => ULift.up x
    | .inr _ => ULift.up y
  have hr : ∀ i, Module.finrank K (LiftedTensorFactors E F i) = 1 := by
    rintro (i | i)
    · simpa only [LiftedTensorFactors, BinaryTensorFactors, finrank_ulift] using hE
    · simpa only [LiftedTensorFactors, BinaryTensorFactors, finrank_ulift] using hF
  have hv : ∀ i, v i ≠ 0 := by
    rintro (i | i)
    · exact fun h ↦ hx (congrArg ULift.down h)
    · exact fun h ↦ hy (congrArg ULift.down h)
  have he : (tensorPairEquiv K E F).symm (x ⊗ₜ[K] y) =
      (⨂ₜ[K] i, v i) := by
    apply (tensorPairEquiv K E F).injective
    simp only [LinearEquiv.apply_symm_apply, tensorPairEquiv_tprod]
    rfl
  rw [injectiveTensorPair_norm_tmul, he,
    (tensor_norm_rational_generators (tensorPairFactors ξ η) hr v hv ω).1]
  simp [tensorPairFactors, v]

variable (ξ : NormFamily S E) (W : Submodule K E) (ω : S.Ω)

/-- The canonical rational determinant map contracts the product of the two
actual rational determinant-generator norms. -/
theorem determinantSequence_norm_rational_tmul_le
    (z : ⋀[K]^(Module.finrank K W) W)
    (u : ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)) :
    ξ.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K]
      determinantSequenceEquiv W (z ⊗ₜ[K] u)) ≤
      (ξ.restrict W).determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z) *
        (ξ.quotient W).determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] u) := by
  let L := (S.ϕ ω).Completion
  let eW := exteriorBaseChangeEquiv K L W (Module.finrank K W)
  let eQ := exteriorBaseChangeEquiv K L (E ⧸ W) (Module.finrank K (E ⧸ W))
  let eE := exteriorBaseChangeEquiv K L E (Module.finrank K E)
  have he : eE.symm (determinantSequenceEquivCompleted W L
      (eW ((1 : L) ⊗ₜ[K] z) ⊗ₜ[L] eQ ((1 : L) ⊗ₜ[K] u))) =
      (1 : L) ⊗ₜ[K] determinantSequenceEquiv W (z ⊗ₜ[K] u) := by
    simp only [eW, eQ, eE, determinantSequenceEquivCompleted, LinearEquiv.trans_apply,
      TensorProduct.congr_tmul, LinearEquiv.symm_apply_apply,
      TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
      one_mul, LinearEquiv.baseChange_tmul]
  have h := ξ.determinantSequence_norm_tmul_le W ω ((1 : L) ⊗ₜ[K] z) ((1 : L) ⊗ₜ[K] u)
  exact (congrArg (ξ.determinant.norm ω) he).symm.le.trans h

/-- The canonical exact-sequence isomorphism has operator norm at most one
for the actual tensor norm on its two determinant lines, in every rank. -/
theorem determinantSequence_operatorNorm_le_one :
    ((ξ.restrict W).determinant.injectiveTensorPair (ξ.quotient W).determinant).operatorNorm
      ξ.determinant ω (determinantSequenceEquiv W).toLinearMap ≤ 1 := by
  let DW := ⋀[K]^(Module.finrank K W) W
  let DQ := ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)
  let α : NormFamily S DW := (ξ.restrict W).determinant
  let β : NormFamily S DQ := (ξ.quotient W).determinant
  let D := α.injectiveTensorPair β
  have hrW : Module.finrank K DW = 1 := determinant_finrank
  have hrQ : Module.finrank K DQ = 1 := determinant_finrank
  have hr : Module.finrank K (DW ⊗[K] DQ) = 1 := by
    rw [Module.finrank_tensorProduct, hrW, hrQ, one_mul]
  let : Nontrivial DW := Module.nontrivial_of_finrank_pos (by rw [hrW]; exact zero_lt_one)
  let : Nontrivial DQ := Module.nontrivial_of_finrank_pos (by rw [hrQ]; exact zero_lt_one)
  obtain ⟨z, hz⟩ := exists_ne (0 : DW)
  obtain ⟨u, hu⟩ := exists_ne (0 : DQ)
  have hn := injectiveTensorPair_norm_rational_generators α β hrW hrQ hz hu ω
  have hp : 0 < D.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (z ⊗ₜ[K] u)) :=
    hn.symm ▸ mul_pos (α.norm_rational_pos ω hz) (β.norm_rational_pos ω hu)
  have hzu : z ⊗ₜ[K] u ≠ 0 := by
    intro he
    rw [he, TensorProduct.tmul_zero, D.norm_zero] at hp
    exact lt_irrefl 0 hp
  have hbound : ξ.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K]
      determinantSequenceEquiv W (z ⊗ₜ[K] u)) ≤
      D.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (z ⊗ₜ[K] u)) :=
    (ξ.determinantSequence_norm_rational_tmul_le W ω z u).trans hn.symm.le
  have hratio : ξ.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K]
      determinantSequenceEquiv W (z ⊗ₜ[K] u)) /
      D.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (z ⊗ₜ[K] u)) ≤ 1 :=
    (div_le_iff₀ hp).2 (by simpa only [one_mul] using hbound)
  exact (D.operatorNorm_eq_div_of_finrank_one ξ.determinant hr
    (determinantSequenceEquiv W).toLinearMap hzu ω).le.trans hratio

end

end ArakelovGeometry.NormFamily

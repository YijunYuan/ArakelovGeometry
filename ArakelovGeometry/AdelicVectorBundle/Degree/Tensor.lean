/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Pair
public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic

import ArakelovGeometry.AdelicVectorBundle.Determinant.Tensor.Comparison
import ArakelovGeometry.AdelicVectorBundle.Tensor.Line
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# The corrected mixed tensor degree inequality

The canonical determinant tensor isomorphism contracts actual determinant
norms. Its rational generator inequality integrates to the degree bound.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

section Algebra

universe wA wB

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (E : Type wA) (F : Type wB) [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Completed determinant tensor transport commutes with original determinant
vectors, rather than only wedges of original tuples. -/
theorem determinantTensorEquivCompleted_tprod_one_tmul
    (s : ⋀[K]^(Module.finrank K E) E) (t : ⋀[K]^(Module.finrank K F) F) :
    determinantTensorEquivCompleted K L E F
      ((⨂ₜ[L] (_ : Fin (Module.finrank K F)),
        exteriorBaseChangeEquiv K L E (Module.finrank K E) ((1 : L) ⊗ₜ[K] s)) ⊗ₜ[L]
        (⨂ₜ[L] (_ : Fin (Module.finrank K E)),
          exteriorBaseChangeEquiv K L F (Module.finrank K F) ((1 : L) ⊗ₜ[K] t))) =
      exteriorBaseChangeEquiv K L (E ⊗[K] F) (Module.finrank K (E ⊗[K] F))
        ((1 : L) ⊗ₜ[K] determinantTensorEquiv K E F
          ((⨂ₜ[K] (_ : Fin (Module.finrank K F)), s) ⊗ₜ[K]
            (⨂ₜ[K] (_ : Fin (Module.finrank K E)), t))) := by
  simp only [determinantTensorEquivCompleted, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, PiTensorProduct.congr_tprod,
    LinearEquiv.symm_apply_apply, tensorBaseChangeEquiv_symm_tprod_tmul,
    Finset.prod_const_one, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    one_mul, LinearEquiv.baseChange_tmul]

/-- Nonzero determinant generators have a nonzero image under the actual
powered determinant tensor map, including empty tensor powers. -/
theorem determinantTensorEquiv_tprod_ne_zero
    {s : ⋀[K]^(Module.finrank K E) E} {t : ⋀[K]^(Module.finrank K F) F}
    (hs : s ≠ 0) (ht : t ≠ 0) :
    determinantTensorEquiv K E F
      ((⨂ₜ[K] (_ : Fin (Module.finrank K F)), s) ⊗ₜ[K]
        (⨂ₜ[K] (_ : Fin (Module.finrank K E)), t)) ≠ 0 := by
  let DE := ⨂[K] (_ : Fin (Module.finrank K F)), ⋀[K]^(Module.finrank K E) E
  let DF := ⨂[K] (_ : Fin (Module.finrank K E)), ⋀[K]^(Module.finrank K F) F
  let s' : DE := ⨂ₜ[K] (_ : Fin (Module.finrank K F)), s
  let t' : DF := ⨂ₜ[K] (_ : Fin (Module.finrank K E)), t
  have hs' : s' ≠ 0 := NormFamily.tensor_generators_ne_zero
    (fun _ ↦ NormFamily.determinant_finrank) (fun _ ↦ s) (fun _ ↦ hs)
  have ht' : t' ≠ 0 := NormFamily.tensor_generators_ne_zero
    (fun _ ↦ NormFamily.determinant_finrank) (fun _ ↦ t) (fun _ ↦ ht)
  let x : ∀ i, LiftedTensorFactors DE DF i := fun i ↦ match i with
    | .inl _ => ULift.up s'
    | .inr _ => ULift.up t'
  have hr : ∀ i, Module.finrank K (LiftedTensorFactors DE DF i) = 1 := by
    rintro (i | i)
    · simpa only [LiftedTensorFactors, BinaryTensorFactors, finrank_ulift] using
        NormFamily.tensor_finrank_one (fun _ ↦ NormFamily.determinant_finrank)
    · simpa only [LiftedTensorFactors, BinaryTensorFactors, finrank_ulift] using
        NormFamily.tensor_finrank_one (fun _ ↦ NormFamily.determinant_finrank)
  have hx : ∀ i, x i ≠ 0 := by
    rintro (i | i)
    · exact fun h ↦ hs' (congrArg ULift.down h)
    · exact fun h ↦ ht' (congrArg ULift.down h)
  have hz := NormFamily.tensor_generators_ne_zero hr x hx
  intro he
  have he' : s' ⊗ₜ[K] t' = 0 := (determinantTensorEquiv K E F).injective
    (he.trans (determinantTensorEquiv K E F).map_zero.symm)
  apply hz
  apply (tensorPairEquiv K DE DF).injective
  simpa only [tensorPairEquiv_tprod, map_zero] using he'

end Algebra

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- The actual rational tensor determinant norm is bounded by the two
actual determinant norm powers. -/
theorem mixedTensorPair_determinant_norm_rational_le
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (s : ⋀[K]^(Module.finrank K E) E) (t : ⋀[K]^(Module.finrank K F) F) :
    (ξ.mixedTensorPair η).determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] determinantTensorEquiv K E F
        ((⨂ₜ[K] (_ : Fin (Module.finrank K F)), s) ⊗ₜ[K]
          (⨂ₜ[K] (_ : Fin (Module.finrank K E)), t))) ≤
      ξ.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] s) ^ Module.finrank K F *
        η.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t) ^ Module.finrank K E := by
  have h := ξ.mixedTensorPair_determinant_norm_le η ω
    (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] s))
    (exteriorBaseChangeEquiv K (S.ϕ ω).Completion F (Module.finrank K F)
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t))
  simpa only [determinantTensorEquivCompleted_tprod_one_tmul,
    LinearEquiv.symm_apply_apply] using h

/-- The actual tensor determinant log norm satisfies the rank-weighted
generator inequality, including degree-zero determinant lines. -/
theorem mixedTensorPair_determinant_logNorm_le
    (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω)
    (s : {x : ⋀[K]^(Module.finrank K E) E // x ≠ 0})
    (t : {x : ⋀[K]^(Module.finrank K F) F // x ≠ 0}) :
    (ξ.mixedTensorPair η).determinant.logNorm
      (determinantTensorEquiv K E F
        ((⨂ₜ[K] (_ : Fin (Module.finrank K F)), s.val) ⊗ₜ[K]
          (⨂ₜ[K] (_ : Fin (Module.finrank K E)), t.val))) ω ≤
      (Module.finrank K F : ℝ) * ξ.determinant.logNorm s.val ω +
        (Module.finrank K E : ℝ) * η.determinant.logNorm t.val ω := by
  have hs := ξ.determinant.norm_rational_pos ω s.property
  have ht := η.determinant.norm_rational_pos ω t.property
  have hq := (ξ.mixedTensorPair η).determinant.norm_rational_pos ω
    (determinantTensorEquiv_tprod_ne_zero K E F s.property t.property)
  have h := Real.log_le_log hq
    (ξ.mixedTensorPair_determinant_norm_rational_le η ω s.val t.val)
  simpa only [logNorm, Real.log_mul (pow_ne_zero _ hs.ne') (pow_ne_zero _ ht.ne'),
    Real.log_pow] using h

end NormFamily

namespace AdelicVectorBundle

/-- The corrected source tensor degree bound on the actual binary mixed tensor.
All ranks are allowed; the source's asserted general equality is false. -/
theorem rank_mul_degree_add_rank_mul_degree_le_degree_mixedTensorPair [S.IsProper]
    (V : AdelicVectorBundle.{w} S) (W : AdelicVectorBundle.{w'} S)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized] :
    (Module.finrank K W : ℝ) * V.degree +
      (Module.finrank K V : ℝ) * W.degree ≤
        (V.mixedTensorPair W).degree := by
  let DV := V.determinantOfMeasurableBase
  let DW := W.determinantOfMeasurableBase
  let T := V.mixedTensorPair W
  let DT := T.determinantOfMeasurableBase
  let s := DV.lineGenerator (hV := (V.determinantOfMeasurableBase_isLine))
  let t := DW.lineGenerator (hV := (W.determinantOfMeasurableBase_isLine))
  let q := determinantTensorEquiv K V W
    ((⨂ₜ[K] (_ : Fin (Module.finrank K W)), s.val) ⊗ₜ[K]
      (⨂ₜ[K] (_ : Fin (Module.finrank K V)), t.val))
  have hq : q ≠ 0 :=
    determinantTensorEquiv_tprod_ne_zero K V W s.property t.property
  have hsI : Integrable (V.toNormFamily.determinant.logNorm s.val) S.v :=
    DV.integrable_logNorm s.val
  have htI : Integrable (W.toNormFamily.determinant.logNorm t.val) S.v :=
    DW.integrable_logNorm t.val
  have hqI : Integrable (T.toNormFamily.determinant.logNorm q) S.v :=
    DT.integrable_logNorm q
  calc
    _ = -(∫ ω, (Module.finrank K W : ℝ) * V.toNormFamily.determinant.logNorm s.val ω +
        (Module.finrank K V : ℝ) * W.toNormFamily.determinant.logNorm t.val ω ∂S.v) := by
      rw [V.degree_eq_neg_integral s, W.degree_eq_neg_integral t,
        integral_add (hsI.const_mul _) (htI.const_mul _), integral_const_mul,
        integral_const_mul]
      ring
    _ ≤ -(∫ ω, T.toNormFamily.determinant.logNorm q ω ∂S.v) := by
      apply neg_le_neg
      apply integral_mono_ae hqI ((hsI.const_mul _).add (htI.const_mul _))
      exact Filter.Eventually.of_forall fun ω ↦
        V.toNormFamily.mixedTensorPair_determinant_logNorm_le W.toNormFamily ω s t
    _ = _ := (T.degree_eq_neg_integral ⟨q, hq⟩).symm

end AdelicVectorBundle

end

end ArakelovGeometry

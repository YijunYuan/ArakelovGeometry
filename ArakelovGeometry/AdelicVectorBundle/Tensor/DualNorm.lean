/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairNorm
import ArakelovGeometry.AdelicVectorBundle.Tensor.Dual
import ArakelovGeometry.Analysis.Tensor.Bilinear
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Actual completed tensor dual norm identities

The canonical algebraic dual distribution acts on the actual completed
fibres of the binary tensor families. The factor norms are arbitrary.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w w'

/-- Binary finite tensor identification commutes with factor equivalences. -/
theorem binaryTensorEquiv_congr {L : Type*} [Field L]
    {V W : Unit ⊕ Unit → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module L (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module L (W i)]
    (e : ∀ i, V i ≃ₗ[L] W i) (z : ⨂[L] i, V i) :
    binaryTensorEquiv L W (PiTensorProduct.congr e z) =
      TensorProduct.map (e (.inl ())).toLinearMap (e (.inr ())).toLinearMap
        (binaryTensorEquiv L V z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    simp only [map_smul, PiTensorProduct.congr_tprod,
      binaryTensorEquiv_tprod, TensorProduct.map_tmul, LinearEquiv.coe_coe]
  | add z t hz ht => simpa only [map_add] using congrArg₂ (· + ·) hz ht

section BinaryEvaluation

variable {L : Type*} [Field L] {X : Unit ⊕ Unit → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Module L (X i)]

/-- Finite and binary canonical dual evaluations agree on all dual tensors. -/
theorem piDualDistrib_binary_tprod (z : ⨂[L] i, Module.Dual L (X i)) (x : ∀ i, X i) :
    PiTensorProduct.dualDistrib z (⨂ₜ[L] i, x i) =
      dualTensorHom L (X (.inl ())) (Module.Dual L (X (.inr ())))
        (binaryTensorEquiv L (fun i ↦ Module.Dual L (X i)) z) (x (.inl ())) (x (.inr ())) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a f =>
    simp only [map_smul, LinearMap.smul_apply, PiTensorProduct.dualDistrib_apply,
      binaryTensorEquiv_tprod, dualTensorHom_apply, Fintype.prod_sum_type, Fintype.prod_unique,
      smul_eq_mul]
  | add z t hz ht => simp only [map_add, LinearMap.add_apply, hz, ht]

end BinaryEvaluation

section Algebra

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (E : Type w) (F : Type w') [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Canonical tensor dual distribution after completed base change is the
actual local bilinear form, on arbitrary completed tensors and test vectors. -/
theorem dualDistrib_baseChange_bilinear_apply
    (z : L ⊗[K] (Module.Dual K E ⊗[K] Module.Dual K F))
    (x : L ⊗[K] E) (y : L ⊗[K] F) :
    dualBaseChangeEquiv K L (E ⊗[K] F)
      ((TensorProduct.dualDistrib K E F).baseChange L z)
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm (x ⊗ₜ[L] y)) =
    dualTensorHom L (L ⊗[K] E) (Module.Dual L (L ⊗[K] F))
      (TensorProduct.map (dualBaseChangeEquiv K L E).toLinearMap
        (dualBaseChangeEquiv K L F).toLinearMap
        (TensorProduct.AlgebraTensorModule.distribBaseChange K L
          (Module.Dual K E) (Module.Dual K F) z)) x y := by
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L
    (Module.Dual K E) (Module.Dual K F)
  obtain ⟨t, rfl⟩ := A.symm.surjective z
  induction t using TensorProduct.inductionOn with
  | add z t hz ht =>
    simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hz ht
  | tmul α β =>
    simpa only [A, LinearEquiv.apply_symm_apply, TensorProduct.map_tmul,
      dualTensorHom_apply, LinearEquiv.coe_coe, LinearMap.smul_apply, smul_eq_mul] using
      dualDistrib_baseChange_apply K L E F α β x y

/-- Lifted completed dual factors identify canonically with the duals of lifted fibres. -/
def tensorPairDualFibreEquiv :
    ∀ i, (L ⊗[K] LiftedTensorFactors (Module.Dual K E) (Module.Dual K F) i) ≃ₗ[L]
      Module.Dual L (L ⊗[K] LiftedTensorFactors E F i)
  | .inl _ => (ULift.moduleEquiv.baseChange K L _ _).trans
      ((dualBaseChangeEquiv K L E).trans (ULift.moduleEquiv.baseChange K L _ _).dualMap)
  | .inr _ => (ULift.moduleEquiv.baseChange K L _ _).trans
      ((dualBaseChangeEquiv K L F).trans (ULift.moduleEquiv.baseChange K L _ _).dualMap)

/-- The lifted dual identification preserves the binary evaluation pairing. -/
theorem tensorPairDualFibreEquiv_eval
    (r : ⨂[L] i, L ⊗[K] LiftedTensorFactors (Module.Dual K E) (Module.Dual K F) i)
    (x : L ⊗[K] LiftedTensorFactors E F (.inl ()))
    (y : L ⊗[K] LiftedTensorFactors E F (.inr ())) :
    dualTensorHom L _ _
      (binaryTensorEquiv L (fun i ↦ Module.Dual L (L ⊗[K] LiftedTensorFactors E F i))
        (PiTensorProduct.congr (tensorPairDualFibreEquiv K L E F) r)) x y =
    dualTensorHom L (L ⊗[K] E) (Module.Dual L (L ⊗[K] F))
      (TensorProduct.map (dualBaseChangeEquiv K L E).toLinearMap
        (dualBaseChangeEquiv K L F).toLinearMap
        (tensorPairFibreEquiv K L (Module.Dual K E) (Module.Dual K F) r))
      ((ULift.moduleEquiv.baseChange K L _ _) x)
      ((ULift.moduleEquiv.baseChange K L _ _) y) := by
  induction r using PiTensorProduct.induction_on with
  | smul_tprod a r =>
    simp only [map_smul, PiTensorProduct.congr_tprod, binaryTensorEquiv_tprod,
      tensorPairFibreEquiv_tprod, TensorProduct.map_tmul, dualTensorHom_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rfl
  | add r s hr hs => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hr hs

/-- Canonical binary dual evaluation commutes with the lifted finite tensor model. -/
theorem tensorPairDualFibre_evaluate
    (z : L ⊗[K] (Module.Dual K E ⊗[K] Module.Dual K F))
    (s : ⨂[L] i, L ⊗[K] LiftedTensorFactors E F i) :
    PiTensorProduct.dualDistrib
      (PiTensorProduct.congr (tensorPairDualFibreEquiv K L E F)
        (tensorBaseChangeEquiv K L (LiftedTensorFactors (Module.Dual K E) (Module.Dual K F))
          ((tensorPairEquiv K (Module.Dual K E)
            (Module.Dual K F)).symm.toLinearMap.baseChange L z)))
      s =
    dualBaseChangeEquiv K L (E ⊗[K] F) ((TensorProduct.dualDistrib K E F).baseChange L z)
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm
        (tensorPairFibreEquiv K L E F s)) := by
  let BD := tensorPairEquiv K (Module.Dual K E) (Module.Dual K F)
  let t := tensorBaseChangeEquiv K L (LiftedTensorFactors (Module.Dual K E) (Module.Dual K F))
    (BD.symm.toLinearMap.baseChange L z)
  have hp : tensorPairFibreEquiv K L (Module.Dual K E) (Module.Dual K F) t =
      TensorProduct.AlgebraTensorModule.distribBaseChange K L
        (Module.Dual K E) (Module.Dual K F) z := by
    have h := DFunLike.congr_fun
      (tensorBaseChangeEquiv_binary K L (Module.Dual K E) (Module.Dual K F))
      (BD.symm.toLinearMap.baseChange L z)
    change tensorPairFibreEquiv K L (Module.Dual K E) (Module.Dual K F) t =
      TensorProduct.AlgebraTensorModule.distribBaseChange K L
      (Module.Dual K E) (Module.Dual K F)
      ((BD.baseChange K L _ _) ((BD.baseChange K L _ _).symm z)) at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  induction s using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    simp only [map_smul, piDualDistrib_binary_tprod]
    congr 1
    change dualTensorHom L _ _
      (binaryTensorEquiv L _ (PiTensorProduct.congr (tensorPairDualFibreEquiv K L E F) t)) _ _ = _
    rw [tensorPairDualFibreEquiv_eval, hp, tensorPairFibreEquiv_tprod]
    exact (dualDistrib_baseChange_bilinear_apply K L E F z _ _).symm
  | add s t hs ht => simp only [map_add, hs, ht]

end Algebra

namespace NormFamily

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The actual injective norm on the completed tensor of the factor duals
is characterized by the actual bilinear bound of canonical dual distribution. -/
theorem injectiveTensorPair_dual_norm_le_iff (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (Module.Dual K E ⊗[K] Module.Dual K F))
    {C : ℝ} (hC : 0 ≤ C) :
    (ξ.dual.injectiveTensorPair η.dual).norm ω z ≤ C ↔
      ∀ (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F),
        ‖dualBaseChangeEquiv K (S.ϕ ω).Completion (E ⊗[K] F)
          ((TensorProduct.dualDistrib K E F).baseChange (S.ϕ ω).Completion z)
          ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion E F).symm
            (x ⊗ₜ[(S.ϕ ω).Completion] y))‖ ≤ C * ξ.norm ω x * η.norm ω y := by
  let L := (S.ϕ ω).Completion
  let X i := L ⊗[K] LiftedTensorFactors E F i
  let D i := L ⊗[K] LiftedTensorFactors (Module.Dual K E) (Module.Dual K F) i
  let : ∀ i, NormedAddCommGroup (X i) := fun i ↦ (tensorPairFactors ξ η i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (tensorPairFactors ξ η i).fibreNormedSpace ω
  let : ∀ i, NormedAddCommGroup (D i) :=
    fun i ↦ (tensorPairFactors ξ.dual η.dual i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (D i) :=
    fun i ↦ (tensorPairFactors ξ.dual η.dual i).fibreNormedSpace ω
  let : ∀ i, NormedAddCommGroup (Module.Dual L (X i)) :=
    fun i ↦ linearDualNormedAddCommGroup (k := L) (E := X i)
  let : ∀ i, NormedSpace L (Module.Dual L (X i)) :=
    fun i ↦ linearDualNormedSpace (k := L) (E := X i)
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := η.fibreNormedAddCommGroup ω
  let := η.fibreNormedSpace ω
  let eE : X (.inl ()) ≃ₗᵢ[L] (L ⊗[K] E) :=
    { toLinearEquiv := ULift.moduleEquiv.baseChange K L _ _, norm_map' := fun _ ↦ rfl }
  let eF : X (.inr ()) ≃ₗᵢ[L] (L ⊗[K] F) :=
    { toLinearEquiv := ULift.moduleEquiv.baseChange K L _ _, norm_map' := fun _ ↦ rfl }
  let e : ∀ i, D i ≃ₗᵢ[L] Module.Dual L (X i) := fun i ↦ match i with
    | .inl _ =>
      { toLinearEquiv := tensorPairDualFibreEquiv K L E F (.inl ())
        norm_map' := fun z ↦ linearMapOperatorSeminorm_comp_isometryEquiv eE
          (dualBaseChangeEquiv K L E ((ULift.moduleEquiv.baseChange K L _ _) z)) }
    | .inr _ =>
      { toLinearEquiv := tensorPairDualFibreEquiv K L E F (.inr ())
        norm_map' := fun z ↦ linearMapOperatorSeminorm_comp_isometryEquiv eF
          (dualBaseChangeEquiv K L F ((ULift.moduleEquiv.baseChange K L _ _) z)) }
  let B := (tensorPairEquiv K (Module.Dual K E) (Module.Dual K F))
  let t := tensorBaseChangeEquiv K L (LiftedTensorFactors (Module.Dual K E) (Module.Dual K F))
    (B.symm.toLinearMap.baseChange L z)
  let q := PiTensorProduct.congr (fun i ↦ (e i).toLinearEquiv) t
  have hn : (ξ.dual.injectiveTensorPair η.dual).norm ω z =
      ArakelovGeometry.injectiveTensorSeminorm q :=
    (injectiveTensorSeminorm_congr_linearIsometryEquiv e t).symm
  have hp : tensorPairFibreEquiv K L (Module.Dual K E) (Module.Dual K F) t =
      TensorProduct.AlgebraTensorModule.distribBaseChange K L
        (Module.Dual K E) (Module.Dual K F) z := by
    have he := DFunLike.congr_fun
      (tensorBaseChangeEquiv_binary K L (Module.Dual K E) (Module.Dual K F))
      (B.symm.toLinearMap.baseChange L z)
    change tensorPairFibreEquiv K L (Module.Dual K E) (Module.Dual K F) t =
      TensorProduct.AlgebraTensorModule.distribBaseChange K L
        (Module.Dual K E) (Module.Dual K F)
        ((B.baseChange K L _ _) ((B.baseChange K L _ _).symm z)) at he
    simpa only [LinearEquiv.apply_symm_apply] using he
  have hb (x : X (.inl ())) (y : X (.inr ())) :
      dualTensorHom L (X (.inl ())) (Module.Dual L (X (.inr ())))
        (binaryTensorEquiv L (fun i ↦ Module.Dual L (X i)) q) x y =
      dualBaseChangeEquiv K L (E ⊗[K] F)
        ((TensorProduct.dualDistrib K E F).baseChange L z)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm
          (eE x ⊗ₜ[L] eF y)) := by
    have hq : q = PiTensorProduct.congr (tensorPairDualFibreEquiv K L E F) t := by
      have heq : (fun i ↦ (e i).toLinearEquiv) = tensorPairDualFibreEquiv K L E F := by
        funext i
        cases i <;> rfl
      exact congrArg (fun es ↦ PiTensorProduct.congr es t) heq
    rw [hq, tensorPairDualFibreEquiv_eval, hp]
    exact (dualDistrib_baseChange_bilinear_apply K L E F z (eE x) (eF y)).symm
  rw [hn]
  have hx (x : X (.inl ())) : ‖x‖ = ξ.norm ω (eE x) := rfl
  have hy (y : X (.inr ())) : ‖y‖ = η.norm ω (eF y) := rfl
  have h := injectiveTensorSeminorm_dual_le_iff (E := X) q hC
  constructor
  · intro hz x y
    have ht := h.mp hz (eE.symm x) (eF.symm y)
    simpa only [hb, hx, hy, LinearIsometryEquiv.apply_symm_apply] using ht
  · intro hz
    apply h.mpr
    intro x y
    rw [hb, hx, hy]
    exact hz (eE x) (eF y)

/-- Canonical dual distribution is an isometry from the injective tensor
of the actual completed duals to the dual of the mixed binary tensor norm.
No admissibility or normalized-Archimedean-field hypothesis is needed. -/
theorem mixedTensorPair_dual_norm_eq_injective (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (Module.Dual K E ⊗[K] Module.Dual K F)) :
    (ξ.mixedTensorPair η).dual.norm ω
      ((TensorProduct.dualDistrib K E F).baseChange (S.ϕ ω).Completion z) =
        (ξ.dual.injectiveTensorPair η.dual).norm ω z := by
  let L := (S.ϕ ω).Completion
  let X i := L ⊗[K] LiftedTensorFactors E F i
  let : ∀ i, NormedAddCommGroup (X i) := fun i ↦ (tensorPairFactors ξ η i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (tensorPairFactors ξ η i).fibreNormedSpace ω
  let q := (TensorProduct.dualDistrib K E F).baseChange L z
  let C := (ξ.dual.injectiveTensorPair η.dual).norm ω z
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L E F
  let B := (tensorPairEquiv K E F).baseChange K L _ _
  let P := tensorPairFibreEquiv K L E F
  let f := (dualBaseChangeEquiv K L (E ⊗[K] F) q).comp
    (A.symm.toLinearMap.comp P.toLinearMap)
  have hC : 0 ≤ C := (ξ.dual.injectiveTensorPair η.dual).norm_nonneg ω z
  have hbound := (injectiveTensorPair_dual_norm_le_iff ξ η ω z hC).mp (le_refl C)
  have hf : ∀ x : ∀ i, X i, ‖f (⨂ₜ[L] i, x i)‖ ≤ C * ∏ i, ‖x i‖ := by
    intro x
    have h := hbound ((ULift.moduleEquiv.baseChange K L _ _) (x (.inl ())))
      ((ULift.moduleEquiv.baseChange K L _ _) (x (.inr ())))
    change ‖dualBaseChangeEquiv K L (E ⊗[K] F) q
      (A.symm (P (⨂ₜ[L] i, x i)))‖ ≤ _
    simp only [P, tensorPairFibreEquiv_tprod, Fintype.prod_sum_type, Fintype.prod_unique]
    change ‖dualBaseChangeEquiv K L (E ⊗[K] F) q
      (A.symm (((ULift.moduleEquiv.baseChange K L _ _) (x (.inl ()))) ⊗ₜ[L]
        ((ULift.moduleEquiv.baseChange K L _ _) (x (.inr ())))))‖ ≤
        C * (ξ.norm ω ((ULift.moduleEquiv.baseChange K L _ _) (x (.inl ()))) *
          η.norm ω ((ULift.moduleEquiv.baseChange K L _ _) (x (.inr ()))))
    exact (h.trans_eq (mul_assoc _ _ _))
  apply le_antisymm
  · apply (ξ.mixedTensorPair η).dual_norm_le ω q hC
    intro u
    let t := tensorBaseChangeEquiv K L (LiftedTensorFactors E F) (B.symm u)
    have hp : P t = A u := by
      have he := DFunLike.congr_fun (tensorBaseChangeEquiv_binary K L E F) (B.symm u)
      change P t = A (B (B.symm u)) at he
      simpa only [LinearEquiv.apply_symm_apply] using he
    have he : f t = dualBaseChangeEquiv K L (E ⊗[K] F) q u := by
      change dualBaseChangeEquiv K L (E ⊗[K] F) q (A.symm (P t)) = _
      rw [hp, LinearEquiv.symm_apply_apply]
    rw [← he]
    by_cases hω : ω ∈ S.Ωfin
    · rw [mixedTensorPair_norm_of_mem_Ωfin ξ η ω hω]
      change ‖f t‖ ≤ C * ArakelovGeometry.injectiveTensorSeminorm t
      have hL (a b : L) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
        refine UniformSpace.Completion.induction_on₂ a b ?_ ?_
        · exact isClosed_le (by fun_prop) (by fun_prop)
        · intro x y
          change ‖(↑x : (S.ϕ ω).Completion) + ↑y‖ ≤
            max ‖(↑x : (S.ϕ ω).Completion)‖ ‖(↑y : (S.ϕ ω).Completion)‖
          rw [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe,
            UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
          exact hω x.ofAbs y.ofAbs
      exact norm_linearMap_le_mul_injective_of_ultrametric_factors f hL hC hf t
    · rw [mixedTensorPair_norm_of_not_mem_Ωfin ξ η ω hω]
      change ‖f t‖ ≤ C * PiTensorProduct.projectiveSeminorm t
      exact norm_linearMap_le_projective_of_tprod_le f hC hf t
  · apply (injectiveTensorPair_dual_norm_le_iff ξ η ω z
      ((ξ.mixedTensorPair η).dual.norm_nonneg ω q)).mpr
    intro x y
    have h := (ξ.mixedTensorPair η).norm_dual_apply_le ω q (A.symm (x ⊗ₜ[L] y))
    apply h.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mixedTensorPair_norm_tmul_completed_le ξ η ω x y)
      ((ξ.mixedTensorPair η).dual.norm_nonneg ω q)

/-- The isometry holds as equality of the actual norm families under the
canonical algebraic dual-tensor identification. -/
theorem mixedTensorPair_dual_pullback (ξ : NormFamily S E) (η : NormFamily S F) :
    (ξ.mixedTensorPair η).dual.pullback (TensorProduct.dualDistrib K E F)
      (by
        simpa only [← TensorProduct.toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe] using
          (TensorProduct.dualDistribEquiv K E F).injective) =
        ξ.dual.injectiveTensorPair η.dual := by
  ext ω z
  exact mixedTensorPair_dual_norm_eq_injective ξ η ω z

end NormFamily

end

end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic
public import ArakelovGeometry.AdelicVectorBundle.Determinant.DualNorm
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian

import ArakelovGeometry.AdelicVectorBundle.Degree.Tensor
import ArakelovGeometry.AdelicVectorBundle.Determinant.Comparison
import ArakelovGeometry.AdelicVectorBundle.Determinant.Duality
import ArakelovGeometry.AdelicVectorBundle.Determinant.Tensor.Comparison
import ArakelovGeometry.AdelicVectorBundle.Determinant.WedgeApproximation
import ArakelovGeometry.AdelicVectorBundle.Tensor.Dual
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Determinants of the actual binary Hermitian tensor norm

The canonical completed tensor and dual maps connect the actual orthogonal
norm to the determinant-line norm product.
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

/-- Canonical products of completed dual vectors in the ordering of the
actual tensor determinant, with the actual dual rank transported explicitly. -/
def completedTensorDualTuple
    (f : Fin (Module.finrank K E) → L ⊗[K] Module.Dual K E)
    (g : Fin (Module.finrank K F) → L ⊗[K] Module.Dual K F) :
    Fin (Module.finrank K (Module.Dual K (E ⊗[K] F))) → L ⊗[K] Module.Dual K (E ⊗[K] F) :=
  fun i ↦ (TensorProduct.dualDistrib K E F).baseChange L
    ((TensorProduct.AlgebraTensorModule.distribBaseChange K L
      (Module.Dual K E) (Module.Dual K F)).symm
      (f (finProdFinEquiv.symm ((finCongr (finrank_mul_eq_tensor K E F)).symm
        (finCongr Subspace.dual_finrank_eq i))).1 ⊗ₜ[L]
       g (finProdFinEquiv.symm ((finCongr (finrank_mul_eq_tensor K E F)).symm
        (finCongr Subspace.dual_finrank_eq i))).2))

/-- The actual completed tensor-dual wedge pairs with the canonical tensor
wedge by the Kronecker determinant identity, including singular and empty tuples. -/
theorem completedTensorDualTuple_pairing_ιMulti
    (f : Fin (Module.finrank K E) → L ⊗[K] Module.Dual K E)
    (g : Fin (Module.finrank K F) → L ⊗[K] Module.Dual K F)
    (x : Fin (Module.finrank K E) → L ⊗[K] E)
    (y : Fin (Module.finrank K F) → L ⊗[K] F) :
    completedDeterminantPairing K L (E ⊗[K] F)
      ((exteriorBaseChangeEquiv K L (Module.Dual K (E ⊗[K] F)) _).symm
        (exteriorPower.ιMulti L _ (completedTensorDualTuple K L E F f g)))
      ((exteriorBaseChangeEquiv K L (E ⊗[K] F) _).symm
        (determinantTensorEquivCompleted K L E F
          ((⨂ₜ[L] (_ : Fin (Module.finrank K F)), exteriorPower.ιMulti L _ x) ⊗ₜ[L]
           (⨂ₜ[L] (_ : Fin (Module.finrank K E)), exteriorPower.ιMulti L _ y)))) =
      (Matrix.of fun i j ↦ dualBaseChangeEquiv K L E (f j) (x i)).det ^ Module.finrank K F *
      (Matrix.of fun i j ↦ dualBaseChangeEquiv K L F (g j) (y i)).det ^ Module.finrank K E := by
  let e := finProdFinEquiv.trans (finCongr (finrank_mul_eq_tensor K E F))
  rw [determinantTensorEquivCompleted_ιMulti, completedDeterminantPairing_ιMulti]
  have hM : (Matrix.of fun i j ↦ dualBaseChangeEquiv K L (E ⊗[K] F)
      (completedTensorDualTuple K L E F f g ((finCongr Subspace.dual_finrank_eq).symm j))
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm
        (x (e.symm i).1 ⊗ₜ[L] y (e.symm i).2))) =
      Matrix.reindex e e (Matrix.kroneckerMap (· * ·)
        (Matrix.of fun i j ↦ dualBaseChangeEquiv K L E (f j) (x i))
        (Matrix.of fun i j ↦ dualBaseChangeEquiv K L F (g j) (y i))) := by
    ext i j
    simp only [completedTensorDualTuple, Equiv.apply_symm_apply,
      dualDistrib_baseChange_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, Matrix.of_apply]
    rfl
  change Matrix.det (Matrix.of fun i j ↦ dualBaseChangeEquiv K L (E ⊗[K] F)
      (completedTensorDualTuple K L E F f g ((finCongr Subspace.dual_finrank_eq).symm j))
      ((TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm
        (x (e.symm i).1 ⊗ₜ[L] y (e.symm i).2))) = _
  rw [hM, Matrix.det_reindex_self, Matrix.det_kronecker]
  simp only [Fintype.card_fin]

/-- The Kronecker pairing formula holds on arbitrary actual completed
primal determinant vectors, including rank-zero scalar lines. -/
theorem completedTensorDualTuple_pairing
    (f : Fin (Module.finrank K E) → L ⊗[K] Module.Dual K E)
    (g : Fin (Module.finrank K F) → L ⊗[K] Module.Dual K F)
    (z : ⋀[L]^(Module.finrank K E) (L ⊗[K] E))
    (t : ⋀[L]^(Module.finrank K F) (L ⊗[K] F)) :
    completedDeterminantPairing K L (E ⊗[K] F)
      ((exteriorBaseChangeEquiv K L (Module.Dual K (E ⊗[K] F)) _).symm
        (exteriorPower.ιMulti L _ (completedTensorDualTuple K L E F f g)))
      ((exteriorBaseChangeEquiv K L (E ⊗[K] F) _).symm
        (determinantTensorEquivCompleted K L E F
          ((⨂ₜ[L] (_ : Fin (Module.finrank K F)), z) ⊗ₜ[L]
           (⨂ₜ[L] (_ : Fin (Module.finrank K E)), t)))) =
      completedDeterminantPairing K L E
        ((exteriorBaseChangeEquiv K L (Module.Dual K E) _).symm
          (exteriorPower.ιMulti L _ (fun i ↦ f (finCongr Subspace.dual_finrank_eq i))))
        ((exteriorBaseChangeEquiv K L E _).symm z) ^ Module.finrank K F *
      completedDeterminantPairing K L F
        ((exteriorBaseChangeEquiv K L (Module.Dual K F) _).symm
          (exteriorPower.ιMulti L _ (fun i ↦ g (finCongr Subspace.dual_finrank_eq i))))
        ((exteriorBaseChangeEquiv K L F _).symm t) ^ Module.finrank K E := by
  let b := (Module.finBasis K E).baseChange L
  let c := (Module.finBasis K F).baseChange L
  let a := determinantCoordinateEquiv b z
  let d := determinantCoordinateEquiv c t
  have hz : z = a • exteriorPower.ιMulti L _ b := by
    rw [← determinantCoordinateEquiv_symm, LinearEquiv.symm_apply_apply]
  have ht : t = d • exteriorPower.ιMulti L _ c := by
    rw [← determinantCoordinateEquiv_symm, LinearEquiv.symm_apply_apply]
  rw [hz, ht]
  simp only [MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, TensorProduct.smul_tmul_smul, map_smul,
    smul_eq_mul]
  rw [completedTensorDualTuple_pairing_ιMulti,
    completedDeterminantPairing_ιMulti, completedDeterminantPairing_ιMulti]
  simp only [Equiv.apply_symm_apply, mul_pow]
  ring

/-- Scalar weights enter the tensor-dual determinant pairing with exactly
the two rank powers, including zero powers. -/
theorem completedTensorDualTuple_pairing_smul
    (a b : L)
    (f : Fin (Module.finrank K E) → L ⊗[K] Module.Dual K E)
    (g : Fin (Module.finrank K F) → L ⊗[K] Module.Dual K F)
    (z : ⋀[L]^(Module.finrank K E) (L ⊗[K] E))
    (t : ⋀[L]^(Module.finrank K F) (L ⊗[K] F)) :
    completedDeterminantPairing K L (E ⊗[K] F)
      ((a ^ Module.finrank K F * b ^ Module.finrank K E) •
        (exteriorBaseChangeEquiv K L (Module.Dual K (E ⊗[K] F)) _).symm
          (exteriorPower.ιMulti L _ (completedTensorDualTuple K L E F f g)))
      ((exteriorBaseChangeEquiv K L (E ⊗[K] F) _).symm
        (determinantTensorEquivCompleted K L E F
          ((⨂ₜ[L] (_ : Fin (Module.finrank K F)), z) ⊗ₜ[L]
           (⨂ₜ[L] (_ : Fin (Module.finrank K E)), t)))) =
      completedDeterminantPairing K L E
        (a • (exteriorBaseChangeEquiv K L (Module.Dual K E) _).symm
          (exteriorPower.ιMulti L _ (fun i ↦ f (finCongr Subspace.dual_finrank_eq i))))
        ((exteriorBaseChangeEquiv K L E _).symm z) ^ Module.finrank K F *
      completedDeterminantPairing K L F
        (b • (exteriorBaseChangeEquiv K L (Module.Dual K F) _).symm
          (exteriorPower.ιMulti L _ (fun i ↦ g (finCongr Subspace.dual_finrank_eq i))))
        ((exteriorBaseChangeEquiv K L F _).symm t) ^ Module.finrank K E := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    completedTensorDualTuple_pairing, mul_pow]
  ring

end Algebra

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- Canonical tensors of completed dual vectors contract in the actual dual
orthogonal norm at every place. -/
theorem orthogonalTensorPair_dual_norm_tmul_le
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω)
    (α : (S.ϕ ω).Completion ⊗[K] Module.Dual K E)
    (β : (S.ϕ ω).Completion ⊗[K] Module.Dual K F) :
    (ξ ⊗ʰ η).dual.norm ω
      ((TensorProduct.dualDistrib K E F).baseChange (S.ϕ ω).Completion
        ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion
          (Module.Dual K E) (Module.Dual K F)).symm
            (α ⊗ₜ[(S.ϕ ω).Completion] β))) ≤
      ξ.dual.norm ω α * η.dual.norm ω β :=
  ((ξ.injectiveTensorPair η).dual_norm_antitone
    (ξ ⊗ʰ η) ω
    (fun z ↦ (ξ.orthogonalTensorPair_norm_bounds η ω z).1) _).trans
      (ξ.injectiveTensorPair_dual_norm_tmul_le η ω α β)

/-- The actual tensor-dual map contracts every completed vector of the
projective product of the actual factor dual norms. -/
theorem orthogonalTensorPair_dual_norm_le_projective
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (Module.Dual K E ⊗[K] Module.Dual K F)) :
    (ξ ⊗ʰ η).dual.norm ω
      ((TensorProduct.dualDistrib K E F).baseChange (S.ϕ ω).Completion z) ≤
        (ξ.dual.projectiveTensorPair η.dual).norm ω z := by
  let L := (S.ϕ ω).Completion
  let X := fun i ↦ L ⊗[K] LiftedTensorFactors (Module.Dual K E) (Module.Dual K F) i
  let : ∀ i, NormedAddCommGroup (X i) :=
    fun i ↦ (tensorPairFactors ξ.dual η.dual i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) :=
    fun i ↦ (tensorPairFactors ξ.dual η.dual i).fibreNormedSpace ω
  let σ := (ξ ⊗ʰ η).dual
  let := σ.fibreNormedAddCommGroup ω
  let := σ.fibreNormedSpace ω
  let A := TensorProduct.AlgebraTensorModule.distribBaseChange K L
    (Module.Dual K E) (Module.Dual K F)
  let B := (tensorPairEquiv K (Module.Dual K E) (Module.Dual K F)).baseChange K L _ _
  let P := tensorPairFibreEquiv K L (Module.Dual K E) (Module.Dual K F)
  let D := (TensorProduct.dualDistrib K E F).baseChange L
  let f := D.comp (A.symm.toLinearMap.comp P.toLinearMap)
  let v := tensorBaseChangeEquiv K L
    (LiftedTensorFactors (Module.Dual K E) (Module.Dual K F)) (B.symm z)
  have hP : P v = A z := by
    have h := DFunLike.congr_fun (tensorBaseChangeEquiv_binary K L
      (Module.Dual K E) (Module.Dual K F)) (B.symm z)
    change P v = A (B (B.symm z)) at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  have hf (x : ∀ i, X i) : ‖f (⨂ₜ[L] i, x i)‖ ≤ (1 : ℝ) * ∏ i, ‖x i‖ := by
    change σ.norm ω (D (A.symm (P (⨂ₜ[L] i, x i)))) ≤ _
    rw [show P (⨂ₜ[L] i, x i) =
      ((ULift.moduleEquiv.baseChange K L _ _) (x (.inl ()))) ⊗ₜ[L]
        ((ULift.moduleEquiv.baseChange K L _ _) (x (.inr ()))) from
      tensorPairFibreEquiv_tprod K L (Module.Dual K E) (Module.Dual K F) x]
    have hprod : (∏ i, ‖x i‖) =
        ξ.dual.norm ω ((ULift.moduleEquiv.baseChange K L _ _) (x (.inl ()))) *
          η.dual.norm ω ((ULift.moduleEquiv.baseChange K L _ _) (x (.inr ()))) := by
      change (∏ i, (tensorPairFactors ξ.dual η.dual i).norm ω (x i)) = _
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, tensorPairFactors, pullback_norm]
      rfl
    rw [one_mul, hprod]
    exact ξ.orthogonalTensorPair_dual_norm_tmul_le η ω _ _
  have h := norm_linearMap_le_projective_of_tprod_le f zero_le_one hf v
  change σ.norm ω (D (A.symm (P v))) ≤ 1 * PiTensorProduct.projectiveSeminorm v at h
  rw [hP, LinearEquiv.symm_apply_apply, one_mul] at h
  exact h

/-- Hadamard and the actual completed tensor-dual bound give a determinant
bound for the canonical ordered dual wedge, in every rank. -/
theorem orthogonalTensorPair_dual_determinant_norm_tuple_le
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω)
    (f : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] Module.Dual K E)
    (g : Fin (Module.finrank K F) → (S.ϕ ω).Completion ⊗[K] Module.Dual K F) :
    (ξ ⊗ʰ η).dual.determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K (E ⊗[K] F)) _).symm
        (exteriorPower.ιMulti (S.ϕ ω).Completion _
          (completedTensorDualTuple K (S.ϕ ω).Completion E F f g))) ≤
      (∏ i, ξ.dual.norm ω (f i)) ^ Module.finrank K F *
        (∏ j, η.dual.norm ω (g j)) ^ Module.finrank K E := by
  let e := finProdFinEquiv.trans (finCongr (finrank_mul_eq_tensor K E F))
  let d := finCongr (Subspace.dual_finrank_eq (K := K) (V := E ⊗[K] F))
  apply ((ξ ⊗ʰ η).dual.determinant_norm_ιMulti_le ω
    (completedTensorDualTuple K (S.ϕ ω).Completion E F f g)).trans
  calc
    _ ≤ ∏ i : Fin (Module.finrank K (Module.Dual K (E ⊗[K] F))),
        ξ.dual.norm ω (f (e.symm (d i)).1) * η.dual.norm ω (g (e.symm (d i)).2) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact (ξ ⊗ʰ η).dual.norm_nonneg ω _
      · intro i hi
        exact ξ.orthogonalTensorPair_dual_norm_tmul_le η ω _ _
    _ = ∏ i : Fin (Module.finrank K (E ⊗[K] F)),
        ξ.dual.norm ω (f (e.symm i).1) * η.dual.norm ω (g (e.symm i).2) :=
      d.prod_comp (fun i ↦ ξ.dual.norm ω (f (e.symm i).1) * η.dual.norm ω (g (e.symm i).2))
    _ = ∏ ij : Fin (Module.finrank K E) × Fin (Module.finrank K F),
        ξ.dual.norm ω (f ij.1) * η.dual.norm ω (g ij.2) :=
      e.symm.prod_comp (fun ij ↦ ξ.dual.norm ω (f ij.1) * η.dual.norm ω (g ij.2))
    _ = _ := by
      simp only [Fintype.prod_prod_type, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]

-- Match the field and algebra instances used by completed determinant maps.
attribute [local instance 50] UniformSpace.Completion.commRing
  UniformSpace.Completion.ring UniformSpace.Completion.instModule
  UniformSpace.Completion.instAddCommGroup
attribute [local irreducible] determinantTensorEquivCompleted exteriorBaseChangeEquiv

/-- Actual completed orthogonal determinant upper bound in every rank. -/
theorem orthogonalTensorPair_determinant_norm_le
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω)
    (z : ⋀[(S.ϕ ω).Completion]^(Module.finrank K E) ((S.ϕ ω).Completion ⊗[K] E))
    (t : ⋀[(S.ϕ ω).Completion]^(Module.finrank K F) ((S.ϕ ω).Completion ⊗[K] F)) :
    (ξ ⊗ʰ η).determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (E ⊗[K] F)
        (Module.finrank K (E ⊗[K] F))).symm
        ((determinantTensorEquivCompleted K (S.ϕ ω).Completion E F).toFun
          ((⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K F)), z) ⊗ₜ[(S.ϕ ω).Completion]
            (⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K E)), t)))) ≤
      ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm z) ^
          Module.finrank K F *
      η.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion F (Module.finrank K F)).symm t) ^
          Module.finrank K E :=
  (determinant_norm_mono _ _ ω
    (fun z ↦ (ξ.orthogonalTensorPair_norm_bounds η ω z).2) _).trans
      (ξ.projectiveTensorPair_determinant_norm_le η ω z t)

/-- Products of the actual factor determinant pairings are bounded by
the actual tensor determinant and the actual factor dual determinants.
Scalar-weighted dual wedge approximation retains the scalar lines in rank zero. -/
theorem orthogonalTensorPair_determinant_pairing_bound
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω)
    (α : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (β : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K F)) (Module.Dual K F)))
    (z : ⋀[(S.ϕ ω).Completion]^(Module.finrank K E) ((S.ϕ ω).Completion ⊗[K] E))
    (t : ⋀[(S.ϕ ω).Completion]^(Module.finrank K F) ((S.ϕ ω).Completion ⊗[K] F)) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E α
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm z)‖ ^ Module.finrank K F *
    ‖completedDeterminantPairing K (S.ϕ ω).Completion F β
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion F _).symm t)‖ ^ Module.finrank K E ≤
    (ξ ⊗ʰ η).determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (E ⊗[K] F) _).symm
        ((determinantTensorEquivCompleted K (S.ϕ ω).Completion E F).toFun
          ((⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K F)), z) ⊗ₜ[(S.ϕ ω).Completion]
           (⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K E)), t)))) *
      (ξ.dual.determinant.norm ω α ^ Module.finrank K F *
       η.dual.determinant.norm ω β ^ Module.finrank K E) := by
  let L := (S.ϕ ω).Completion
  let σ := ξ.orthogonalTensorPair η
  let w := (exteriorBaseChangeEquiv K L (E ⊗[K] F) _).symm
    ((determinantTensorEquivCompleted K L E F).toFun
      ((⨂ₜ[L] (_ : Fin (Module.finrank K F)), z) ⊗ₜ[L]
       (⨂ₜ[L] (_ : Fin (Module.finrank K E)), t)))
  let C := ξ.dual.determinant.norm ω α
  let D := η.dual.determinant.norm ω β
  let P := ‖completedDeterminantPairing K L E α
      ((exteriorBaseChangeEquiv K L E _).symm z)‖ ^ Module.finrank K F *
    ‖completedDeterminantPairing K L F β
      ((exteriorBaseChangeEquiv K L F _).symm t)‖ ^ Module.finrank K E
  change P ≤ σ.determinant.norm ω w * (C ^ Module.finrank K F * D ^ Module.finrank K E)
  have hε (ε : ℝ) (hε : 0 < ε) :
      P ≤ σ.determinant.norm ω w *
        ((C + ε) ^ Module.finrank K F * (D + ε) ^ Module.finrank K E) := by
    obtain ⟨a, f₀, hα, hf₀⟩ := ξ.dual.exists_smul_determinant_ιMulti_norm_lt ω α hε
    obtain ⟨b, g₀, hβ, hg₀⟩ := η.dual.exists_smul_determinant_ιMulti_norm_lt ω β hε
    let dE := finCongr (Subspace.dual_finrank_eq (K := K) (V := E))
    let dF := finCongr (Subspace.dual_finrank_eq (K := K) (V := F))
    let f := fun i ↦ f₀ (dE.symm i)
    let g := fun j ↦ g₀ (dF.symm j)
    let u := (exteriorBaseChangeEquiv K L (Module.Dual K (E ⊗[K] F)) _).symm
      (exteriorPower.ιMulti L _ (completedTensorDualTuple K L E F f g))
    let scl := a ^ Module.finrank K F * b ^ Module.finrank K E
    have hf : (∏ i, ξ.dual.norm ω (f i)) = ∏ i, ξ.dual.norm ω (f₀ i) :=
      dE.symm.prod_comp (fun i ↦ ξ.dual.norm ω (f₀ i))
    have hg : (∏ i, η.dual.norm ω (g i)) = ∏ i, η.dual.norm ω (g₀ i) :=
      dF.symm.prod_comp (fun i ↦ η.dual.norm ω (g₀ i))
    have hp : completedDeterminantPairing K L (E ⊗[K] F) (scl • u) w =
        completedDeterminantPairing K L E α
          ((exteriorBaseChangeEquiv K L E _).symm z) ^ Module.finrank K F *
        completedDeterminantPairing K L F β
          ((exteriorBaseChangeEquiv K L F _).symm t) ^ Module.finrank K E := by
      have h := completedTensorDualTuple_pairing_smul K L E F a b f g z t
      simp only [f, g, dE, dF, Equiv.symm_apply_apply] at h
      have hE := congrArg (fun q ↦ completedDeterminantPairing K L E q
        ((exteriorBaseChangeEquiv K L E _).symm z) ^ Module.finrank K F) hα
      have hF := congrArg (fun q ↦ completedDeterminantPairing K L F q
        ((exteriorBaseChangeEquiv K L F _).symm t) ^ Module.finrank K E) hβ
      exact h.trans (congrArg₂ (fun q r : L ↦ q * r) hE hF)
    have hu : σ.dual.determinant.norm ω (scl • u) ≤
        (‖a‖ * ∏ i, ξ.dual.norm ω (f₀ i)) ^ Module.finrank K F *
        (‖b‖ * ∏ i, η.dual.norm ω (g₀ i)) ^ Module.finrank K E := by
      rw [σ.dual.determinant.norm_smul]
      have h := ξ.orthogonalTensorPair_dual_determinant_norm_tuple_le η ω f g
      change σ.dual.determinant.norm ω u ≤ _ at h
      rw [hf, hg] at h
      calc
        _ ≤ ‖scl‖ * ((∏ i, ξ.dual.norm ω (f₀ i)) ^ Module.finrank K F *
            (∏ i, η.dual.norm ω (g₀ i)) ^ Module.finrank K E) :=
          mul_le_mul_of_nonneg_left h (_root_.norm_nonneg scl)
        _ = _ := by simp only [scl, norm_mul, norm_pow, mul_pow]; ring
    calc
      P = ‖completedDeterminantPairing K L (E ⊗[K] F) (scl • u) w‖ := by
        rw [hp, norm_mul, norm_pow, norm_pow]
      _ ≤ σ.determinant.norm ω w * σ.dual.determinant.norm ω (scl • u) :=
        (ξ.orthogonalTensorPair_isHermitian η).norm_completedDeterminantPairing_le
          σ ω (scl • u) w
      _ ≤ σ.determinant.norm ω w *
          ((C + ε) ^ Module.finrank K F * (D + ε) ^ Module.finrank K E) := by
        apply mul_le_mul_of_nonneg_left _ (σ.determinant.norm_nonneg ω w)
        apply hu.trans
        exact mul_le_mul
          (pow_le_pow_left₀ (mul_nonneg (_root_.norm_nonneg a)
            (Finset.prod_nonneg fun i _ ↦ ξ.dual.norm_nonneg ω (f₀ i))) hf₀.le _)
          (pow_le_pow_left₀ (mul_nonneg (_root_.norm_nonneg b)
            (Finset.prod_nonneg fun i _ ↦ η.dual.norm_nonneg ω (g₀ i))) hg₀.le _)
          (pow_nonneg (mul_nonneg (_root_.norm_nonneg b)
            (Finset.prod_nonneg fun i _ ↦ η.dual.norm_nonneg ω (g₀ i))) _)
          (pow_nonneg (add_nonneg (ξ.dual.determinant.norm_nonneg ω α) hε.le) _)
  have hlim : Filter.Tendsto (fun n : ℕ ↦ σ.determinant.norm ω w *
      ((C + 1 / ((n : ℝ) + 1)) ^ Module.finrank K F *
       (D + 1 / ((n : ℝ) + 1)) ^ Module.finrank K E))
      Filter.atTop (nhds (σ.determinant.norm ω w *
        (C ^ Module.finrank K F * D ^ Module.finrank K E))) := by
    simpa only [add_zero] using
      (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add C).pow
        (Module.finrank K F) |>.mul
        (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add D).pow
          (Module.finrank K E))).const_mul (σ.determinant.norm ω w)
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun n ↦
    hε _ (one_div_pos.mpr (by positivity)))

/-- The canonical completed determinant tensor map preserves the actual
Hermitian determinant norm product in every rank and on all determinant vectors. -/
theorem orthogonalTensorPair_determinant_norm_eq
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω)
    (z : ⋀[(S.ϕ ω).Completion]^(Module.finrank K E) ((S.ϕ ω).Completion ⊗[K] E))
    (t : ⋀[(S.ϕ ω).Completion]^(Module.finrank K F) ((S.ϕ ω).Completion ⊗[K] F)) :
    (ξ ⊗ʰ η).determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (E ⊗[K] F)
        (Module.finrank K (E ⊗[K] F))).symm
        ((determinantTensorEquivCompleted K (S.ϕ ω).Completion E F).toFun
          ((⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K F)), z) ⊗ₜ[(S.ϕ ω).Completion]
            (⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K E)), t)))) =
      ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)).symm z) ^
          Module.finrank K F *
      η.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion F (Module.finrank K F)).symm t) ^
          Module.finrank K E := by
  apply le_antisymm (ξ.orthogonalTensorPair_determinant_norm_le η ω z t)
  let bE := Module.finBasisOfFinrankEq K
    (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E))
    (determinant_finrank (K := K) (E := Module.Dual K E))
  let bF := Module.finBasisOfFinrankEq K
    (⋀[K]^(Module.finrank K (Module.Dual K F)) (Module.Dual K F))
    (determinant_finrank (K := K) (E := Module.Dual K F))
  let α := (1 : (S.ϕ ω).Completion) ⊗ₜ[K] bE 0
  let β := (1 : (S.ϕ ω).Completion) ⊗ₜ[K] bF 0
  let P := ξ.determinant.norm ω ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm z)
  let Q := η.determinant.norm ω ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion F _).symm t)
  let C := ξ.dual.determinant.norm ω α
  let D := η.dual.determinant.norm ω β
  have hC : 0 < C := ξ.dual.determinant.norm_rational_pos ω (bE.ne_zero 0)
  have hD : 0 < D := η.dual.determinant.norm_rational_pos ω (bF.ne_zero 0)
  have h := ξ.orthogonalTensorPair_determinant_pairing_bound η ω α β z t
  let R := (ξ ⊗ʰ η).determinant.norm ω
    ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (E ⊗[K] F) _).symm
      ((determinantTensorEquivCompleted K (S.ϕ ω).Completion E F).toFun
        ((⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K F)), z) ⊗ₜ[(S.ϕ ω).Completion]
         (⨂ₜ[(S.ϕ ω).Completion] (_ : Fin (Module.finrank K E)), t))))
  have hpair := congrArg₂ (fun q r : ℝ ↦ q ^ Module.finrank K F * r ^ Module.finrank K E)
    (hξ.norm_completedDeterminantPairing_eq ξ ω α
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm z))
    (hη.norm_completedDeterminantPairing_eq η ω β
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion F _).symm t))
  have h' : (P ^ Module.finrank K F * Q ^ Module.finrank K E) *
      (C ^ Module.finrank K F * D ^ Module.finrank K E) ≤
      R * (C ^ Module.finrank K F * D ^ Module.finrank K E) := by
    calc
      _ = (P * C) ^ Module.finrank K F * (Q * D) ^ Module.finrank K E := by
        simp only [mul_pow]
        ring
      _ = _ := hpair.symm
      _ ≤ _ := h
  exact le_of_mul_le_mul_right h' (mul_pos (pow_pos hC _) (pow_pos hD _))

/-- The actual rational tensor determinant norm is the product of the two
actual determinant norm powers for Hermitian factors. -/
theorem orthogonalTensorPair_determinant_norm_rational_eq
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω)
    (s : ⋀[K]^(Module.finrank K E) E) (t : ⋀[K]^(Module.finrank K F) F) :
    (ξ ⊗ʰ η).determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] determinantTensorEquiv K E F
        ((⨂ₜ[K] (_ : Fin (Module.finrank K F)), s) ⊗ₜ[K]
          (⨂ₜ[K] (_ : Fin (Module.finrank K E)), t))) =
      ξ.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] s) ^ Module.finrank K F *
        η.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t) ^ Module.finrank K E := by
  have h := ξ.orthogonalTensorPair_determinant_norm_eq η ω
    (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (Module.finrank K E)
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] s))
    (exteriorBaseChangeEquiv K (S.ϕ ω).Completion F (Module.finrank K F)
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t))
  simpa only [LinearEquiv.toFun_eq_coe, determinantTensorEquivCompleted_tprod_one_tmul,
    LinearEquiv.symm_apply_apply] using h

/-- The actual tensor determinant log norm is the rank-weighted sum of
factor determinant log norms. All ranks, including zero, are retained. -/
theorem orthogonalTensorPair_determinant_logNorm_eq
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ω : S.Ω)
    (s : {x : ⋀[K]^(Module.finrank K E) E // x ≠ 0})
    (t : {x : ⋀[K]^(Module.finrank K F) F // x ≠ 0}) :
    (ξ ⊗ʰ η).determinant.logNorm
      (determinantTensorEquiv K E F
        ((⨂ₜ[K] (_ : Fin (Module.finrank K F)), s.val) ⊗ₜ[K]
          (⨂ₜ[K] (_ : Fin (Module.finrank K E)), t.val))) ω =
      (Module.finrank K F : ℝ) * ξ.determinant.logNorm s.val ω +
        (Module.finrank K E : ℝ) * η.determinant.logNorm t.val ω := by
  have hs := ξ.determinant.norm_rational_pos ω s.property
  have ht := η.determinant.norm_rational_pos ω t.property
  have h := congrArg Real.log
    (ξ.orthogonalTensorPair_determinant_norm_rational_eq η ω s.val t.val)
  simpa only [logNorm, Real.log_mul (pow_ne_zero _ hs.ne') (pow_ne_zero _ ht.ne'),
    Real.log_pow] using h

end NormFamily

namespace AdelicVectorBundle

/-- Source equation (4.35): the actual orthogonal tensor bundle has the
rank-weighted degree sum. All analytic fields are supplied by its constructor. -/
theorem degree_orthogonalTensorPair [S.IsProper]
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.IsHermitian] [hW : W.IsHermitian] :
    (V ⊗ʰ W).degree =
      (Module.finrank K W : ℝ) * V.degree +
        (Module.finrank K V : ℝ) * W.degree := by
  let DV := V.determinantOfNormMeasurability
  let DW := W.determinantOfNormMeasurability
  let T := V.orthogonalTensorPair W
  let s := DV.lineGenerator (hV := (V.determinantOfNormMeasurability_isLine))
  let t := DW.lineGenerator (hV := (W.determinantOfNormMeasurability_isLine))
  let q := determinantTensorEquiv K V W
    ((⨂ₜ[K] (_ : Fin (Module.finrank K W)), s.val) ⊗ₜ[K]
      (⨂ₜ[K] (_ : Fin (Module.finrank K V)), t.val))
  have hq : q ≠ 0 := determinantTensorEquiv_tprod_ne_zero K V W s.property t.property
  have hsI : Integrable (V.toNormFamily.determinant.logNorm s.val) S.v :=
    DV.integrable_logNorm s.val
  have htI : Integrable (W.toNormFamily.determinant.logNorm t.val) S.v :=
    DW.integrable_logNorm t.val
  calc
    T.degree = -(∫ ω, T.toNormFamily.determinant.logNorm q ω ∂S.v) :=
      T.degree_eq_neg_integral ⟨q, hq⟩
    _ = -(∫ ω, (Module.finrank K W : ℝ) * V.toNormFamily.determinant.logNorm s.val ω +
        (Module.finrank K V : ℝ) * W.toNormFamily.determinant.logNorm t.val ω ∂S.v) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦
        V.toNormFamily.orthogonalTensorPair_determinant_logNorm_eq W.toNormFamily
           ω s t
    _ = _ := by
      rw [V.degree_eq_neg_integral s, W.degree_eq_neg_integral t,
        integral_add (hsI.const_mul _) (htI.const_mul _), integral_const_mul,
        integral_const_mul]
      ring

end AdelicVectorBundle

end

end ArakelovGeometry

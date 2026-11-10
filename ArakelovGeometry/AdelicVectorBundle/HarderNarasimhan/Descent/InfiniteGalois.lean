/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module


public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Descent.Subspace
public import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual subspace descent over infinite Galois extensions

Genuine finite Galois coordinate fields and actual automorphism extension
reduce stable-subspace descent to the accepted finite trace-dual producer.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.HermitianAbsoluteDescent

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup E] [Module K E]

/-- The actual finite intermediate-field tensor inclusion. -/
def finiteGaloisTensorInclusion (F : FiniteGaloisIntermediateField K L) :
    F ⊗[K] E →ₗ[F] L ⊗[K] E :=
  (LinearMap.restrictScalars F
    (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap).comp
    (TensorProduct.mk F L (F ⊗[K] E) 1)

/-- The actual inclusion embeds the first scalar of every pure tensor. -/
@[simp]
theorem finiteGaloisTensorInclusion_tmul (F : FiniteGaloisIntermediateField K L)
    (a : F) (e : E) : finiteGaloisTensorInclusion F (a ⊗ₜ[K] e) =
      (a : L) ⊗ₜ[K] e := by
  change TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    ((1 : L) ⊗ₜ[F] (a ⊗ₜ[K] e)) = _
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    Algebra.smul_def, mul_one]
  rfl

/-- Every actual tensor has coordinates in a genuine finite Galois field. -/
theorem exists_finiteGaloisStage_tensor_lift [IsGalois K L] [FiniteDimensional K E]
    (z : L ⊗[K] E) :
    ∃ F : FiniteGaloisIntermediateField K L, ∃ y : F ⊗[K] E,
      finiteGaloisTensorInclusion F y = z := by
  classical
  let b := Module.finBasis K E
  let c := (b.baseChange L).equivFun z
  let F := FiniteGaloisIntermediateField.adjoin K (Set.range c)
  have hc (j) : c j ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  let y : F ⊗[K] E := (b.baseChange F).equivFun.symm (fun j => ⟨c j, hc j⟩)
  refine ⟨F, y, ?_⟩
  rw [← (b.baseChange L).sum_repr z]
  simp only [y, Module.Basis.equivFun_symm_apply, Module.Basis.baseChange_apply,
    map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    finiteGaloisTensorInclusion_tmul]
  rfl

/-- Finite-field tensor inclusion commutes with actual extending automorphisms. -/
theorem finiteGaloisTensorInclusion_semilinear
    (F : FiniteGaloisIntermediateField K L) (τ : L ≃ₐ[K] L) (σ : F ≃ₐ[K] F)
    (hτ : AlgEquiv.restrictNormalHom F τ = σ) (y : F ⊗[K] E) :
    finiteGaloisTensorInclusion F (scalarExtensionSemilinearEquiv σ y) =
      scalarExtensionSemilinearEquiv τ (finiteGaloisTensorInclusion F y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a e =>
    simp only [scalarExtensionSemilinearEquiv_tmul, finiteGaloisTensorInclusion_tmul]
    have ha : (σ a : L) = τ (a : L) := by
      rw [← hτ]
      exact AlgEquiv.restrictNormalHom_apply F.toIntermediateField τ a
    rw [ha]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Stable actual subspaces descend over possibly infinite Galois extensions. -/
theorem baseChange_rationalPart_eq_of_stable_of_isGalois
    [IsGalois K L] [FiniteDimensional K E] (W : Submodule L (L ⊗[K] E))
    (hW : ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] E), x ∈ W →
      scalarExtensionSemilinearEquiv σ x ∈ W) :
    (rationalPart W).baseChange L = W := by
  classical
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    exact he
  · intro x hx
    obtain ⟨F, y, hy⟩ := exists_finiteGaloisStage_tensor_lift x
    let WF := (W.restrictScalars F).comap (finiteGaloisTensorInclusion F)
    have hWF (σ : F ≃ₐ[K] F) (z : F ⊗[K] E) (hz : z ∈ WF) :
        scalarExtensionSemilinearEquiv σ z ∈ WF := by
      obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective L σ
      change finiteGaloisTensorInclusion F (scalarExtensionSemilinearEquiv σ z) ∈ W
      rw [finiteGaloisTensorInclusion_semilinear F τ σ hτ]
      exact hW τ _ hz
    have hU : rationalPart WF = rationalPart W := by
      ext e
      change finiteGaloisTensorInclusion F ((1 : F) ⊗ₜ[K] e) ∈ W ↔
        (1 : L) ⊗ₜ[K] e ∈ W
      simp only [finiteGaloisTensorInclusion_tmul, IntermediateField.coe_one]
    have hyF : y ∈ WF := by
      change finiteGaloisTensorInclusion F y ∈ W
      rwa [hy]
    rw [← baseChange_rationalPart_eq_of_stable WF hWF, hU] at hyF
    have hspan : (rationalPart W).baseChange F ≤
        (((rationalPart W).baseChange L).restrictScalars F).comap
          (finiteGaloisTensorInclusion F) := by
      rw [Submodule.baseChange_eq_span, Submodule.span_le]
      rintro _ ⟨e, he, rfl⟩
      change finiteGaloisTensorInclusion F ((1 : F) ⊗ₜ[K] e) ∈
        (rationalPart W).baseChange L
      simp only [finiteGaloisTensorInclusion_tmul, IntermediateField.coe_one]
      exact Submodule.tmul_mem_baseChange_of_mem _ he
    rw [← hy]
    exact hspan hyF

/-- The descended original subspace is unique in the actual tensor space. -/
theorem existsUnique_baseChange_eq_of_stable_of_isGalois
    [IsGalois K L] [FiniteDimensional K E] (W : Submodule L (L ⊗[K] E))
    (hW : ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] E), x ∈ W →
      scalarExtensionSemilinearEquiv σ x ∈ W) :
    ∃! U : Submodule K E, U.baseChange L = W := by
  refine ⟨rationalPart W, baseChange_rationalPart_eq_of_stable_of_isGalois W hW, ?_⟩
  intro U hU
  exact Submodule.baseChange_injective
    (hU.trans (baseChange_rationalPart_eq_of_stable_of_isGalois W hW).symm)

/-- Perfectness produces the infinite Galois structure of an algebraic closure. -/
theorem baseChange_rationalPart_eq_of_stable_of_isAlgClosed
    [PerfectField K] [Algebra.IsAlgebraic K L] [IsAlgClosed L] [FiniteDimensional K E]
    (W : Submodule L (L ⊗[K] E))
    (hW : ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] E), x ∈ W →
      scalarExtensionSemilinearEquiv σ x ∈ W) :
    (rationalPart W).baseChange L = W := by
  let : IsAlgClosure K L := { isAlgClosed := inferInstance, isAlgebraic := inferInstance }
  let : IsGalois K L := IsGalois.mk
  exact baseChange_rationalPart_eq_of_stable_of_isGalois W hW

/-- Closed-extension descent produces the unique actual original subspace. -/
theorem existsUnique_baseChange_eq_of_stable_of_isAlgClosed
    [PerfectField K] [Algebra.IsAlgebraic K L] [IsAlgClosed L] [FiniteDimensional K E]
    (W : Submodule L (L ⊗[K] E))
    (hW : ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] E), x ∈ W →
      scalarExtensionSemilinearEquiv σ x ∈ W) :
    ∃! U : Submodule K E, U.baseChange L = W := by
  let : IsAlgClosure K L := { isAlgClosed := inferInstance, isAlgebraic := inferInstance }
  let : IsGalois K L := IsGalois.mk
  exact existsUnique_baseChange_eq_of_stable_of_isGalois W hW

end ArakelovGeometry.HermitianAbsoluteDescent

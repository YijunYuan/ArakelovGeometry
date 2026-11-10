/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.FiniteIntermediateField
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.CategoryTheory.Category.Init
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
/-!
# Finite fields of definition for tensor subspaces

Finite families of actual scalar-extended vectors and subspaces descend to one
finite intermediate field, without a separability hypothesis. The canonical
tensor tower identity preserves their dimensions, inclusions and flag endpoints.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v w wE
variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {E : Type wE} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Finitely many actual tensor coordinate families descend to one finite
intermediate field under the canonical tensor tower identity. -/
theorem exists_finiteStage_tensor_lifts {ι : Type v} [Finite ι]
    (z : ι → L ⊗[K] E) :
    ∃ F : AdelicStructure.FiniteIntermediateField K L, ∃ y : ι → F ⊗[K] E,
      ∀ i, TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
        ((1 : L) ⊗ₜ[F] y i) = z i := by
  classical
  let b := Module.finBasis K E
  let c := fun i : ι × Fin (Module.finrank K E) => (b.baseChange L).equivFun (z i.1) i.2
  let A := IntermediateField.adjoin K (Set.range c)
  have hc (i) : c i ∈ A := IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  let : FiniteDimensional K A := IntermediateField.finiteDimensional_adjoin
    (fun a _ => Algebra.IsIntegral.isIntegral a)
  let F : AdelicStructure.FiniteIntermediateField K L := ⟨A, inferInstance⟩
  let y : ι → F ⊗[K] E :=
    fun i => (b.baseChange F).equivFun.symm (fun j => ⟨c (i, j), hc (i, j)⟩)
  refine ⟨F, y, ?_⟩
  intro i
  rw [← (b.baseChange L).sum_repr (z i)]
  simp only [y, Module.Basis.equivFun_symm_apply, Module.Basis.baseChange_apply,
    TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, one_smul]
  rfl

/-- Canonical tensor-tower base change preserves the dimension of every
actual subspace over the finite intermediate field. -/
theorem finrank_map_baseChange_cancelBaseChange
    (F : AdelicStructure.FiniteIntermediateField K L) (B : Submodule F (F ⊗[K] E)) :
    Module.finrank L
      (Submodule.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
        (B.baseChange L)) =
      Module.finrank F B := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  calc
    Module.finrank L (Submodule.map e.toLinearMap (B.baseChange L)) =
        Module.finrank L (B.baseChange L) :=
      (Submodule.equivMapOfInjective e.toLinearMap e.injective _).finrank_eq.symm
    _ = Module.finrank L (L ⊗[F] B) :=
      (Submodule.toBaseChange.toLinearEquiv L B).finrank_eq.symm
    _ = Module.finrank F B := Module.finrank_baseChange

omit [FiniteDimensional K E] in
/-- Canonical tensor-tower base change reflects and preserves actual
subspace inclusions. -/
theorem map_baseChange_cancelBaseChange_le_iff
    (F : AdelicStructure.FiniteIntermediateField K L)
    (B C : Submodule F (F ⊗[K] E)) :
    Submodule.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
        (B.baseChange L) ≤
      Submodule.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
        (C.baseChange L) ↔ B ≤ C := by
  rw [Submodule.map_le_map_iff_of_injective
    (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).injective]
  exact (Submodule.baseChangeOrderEmbedding F (F ⊗[K] E) L).le_iff_le

/-- Every finite family of actual extended subspaces has one finite field
of definition, with literal equality after canonical base change. -/
theorem exists_finiteStage_subspaces {ι : Type v} [Finite ι]
    (A : ι → Submodule L (L ⊗[K] E)) :
    ∃ F : AdelicStructure.FiniteIntermediateField K L,
      ∃ B : ι → Submodule F (F ⊗[K] E),
        ∀ i, Submodule.map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
          ((B i).baseChange L) = A i := by
  classical
  let b := fun i => Module.finBasis L (A i)
  let z := fun p : (Σ i : ι, Fin (Module.finrank L (A i))) =>
    (b p.1 p.2 : L ⊗[K] E)
  obtain ⟨F, y, hy⟩ := exists_finiteStage_tensor_lifts z
  let B := fun i => Submodule.span F (Set.range (fun j => y ⟨i, j⟩))
  refine ⟨F, B, ?_⟩
  intro i
  simp only [B, Submodule.baseChange_span, Submodule.map_span, Set.image_image]
  have hset :
      (fun x => (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
        (((TensorProduct.mk F L (F ⊗[K] E)) 1) x)) ''
          Set.range (fun j => y ⟨i, j⟩) =
      (A i).subtype '' Set.range (b i) := by
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨b i j, ⟨j, rfl⟩, (hy ⟨i, j⟩).symm⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨y ⟨i, j⟩, ⟨j, rfl⟩, hy ⟨i, j⟩⟩
  rw [hset, Submodule.span_image, (b i).span_eq, Submodule.map_top]
  exact (A i).range_subtype

/-- Every actual finite strict exhaustive flag descends to one finite
intermediate field with all dimensions, strictness and endpoints preserved. -/
theorem exists_finiteStage_flag (n : ℕ)
    (A : Fin (n + 1) → Submodule L (L ⊗[K] E)) (hA : StrictMono A)
    (hbot : A 0 = ⊥) (htop : A (Fin.last n) = ⊤) :
    ∃ F : AdelicStructure.FiniteIntermediateField K L,
      ∃ B : Fin (n + 1) → Submodule F (F ⊗[K] E),
        (∀ i, Submodule.map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
          ((B i).baseChange L) = A i) ∧
        (∀ i, Module.finrank F (B i) = Module.finrank L (A i)) ∧
        StrictMono B ∧ B 0 = ⊥ ∧ B (Fin.last n) = ⊤ := by
  obtain ⟨F, B, he⟩ := exists_finiteStage_subspaces A
  refine ⟨F, B, he, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← he i]
    exact (finrank_map_baseChange_cancelBaseChange F (B i)).symm
  · intro i j hij
    apply lt_of_le_not_ge
    · apply (map_baseChange_cancelBaseChange_le_iff F (B i) (B j)).mp
      rw [he i, he j]
      exact (hA hij).le
    · intro hji
      have h := (map_baseChange_cancelBaseChange_le_iff F (B j) (B i)).mpr hji
      rw [he j, he i] at h
      exact (not_le_of_gt (hA hij)) h
  · apply Submodule.baseChange_injective (A := L)
    apply Submodule.map_injective_of_injective
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).injective
    simp only [he 0, hbot, Submodule.baseChange_bot, Submodule.map_bot]
  · apply Submodule.baseChange_injective (A := L)
    apply Submodule.map_injective_of_injective
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).injective
    rw [he (Fin.last n), htop, Submodule.baseChange_top, Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).surjective).symm
end ArakelovGeometry

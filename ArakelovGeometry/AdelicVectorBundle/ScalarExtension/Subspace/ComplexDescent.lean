/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.FiniteIntermediateField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Archimedean
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.Descent
import Mathlib.CategoryTheory.Category.Init

/-!
# Complexifying finite fields of definition for actual subspaces

An actual finite field of definition can be enlarged by a finite field
containing a square root of minus one. The canonical inclusion tensor map
transports each descended subspace to its span over the enlarged field, and
its final tensor-tower image is unchanged on every vector. Dimensions,
inclusions and the endpoints of actual exhaustive flags are preserved.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v w wE
variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [IsAlgClosed L]

/-- Every actual finite intermediate field is contained in one finite
intermediate field with a square root of minus one, in every characteristic. -/
theorem exists_complexFiniteStage_ge (F : AdelicStructure.FiniteIntermediateField K L) :
    ∃ G : AdelicStructure.FiniteIntermediateField K L,
      F.toIntermediateField ≤ G.toIntermediateField ∧ ∃ a : G, a ^ 2 = -1 := by
  obtain ⟨H, a, ha⟩ := exists_finiteStage_sqrt_neg_one (K := K) (L := L)
  refine ⟨F.sup H, F.left_le_sup H, ?_⟩
  let f := IntermediateField.inclusion (F.right_le_sup H)
  exact ⟨f a, by simpa only [map_pow, map_neg, map_one] using congrArg f ha⟩

variable {E : Type wE} [AddCommGroup E] [Module K E]

omit [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Naturality of the genuine inclusion tensor map, on every vector. -/
private theorem complexDescent_tensor_inclusion
    (F G : AdelicStructure.FiniteIntermediateField K L)
    (hFG : F.toIntermediateField ≤ G.toIntermediateField) (z : F ⊗[K] E) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange K G L L E
      ((1 : L) ⊗ₜ[G] TensorProduct.map (IntermediateField.inclusion hFG).toLinearMap
        (LinearMap.id : E →ₗ[K] E) z) =
    TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E ((1 : L) ⊗ₜ[F] z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a e =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, hx, hy]

omit [Algebra.IsAlgebraic K L] [IsAlgClosed L] in
/-- Enlarging the field by the genuine inclusion tensor map preserves the
literal final subspace image; no choice of basis is required. -/
private theorem complexDescent_span_inclusion_image
    (F G : AdelicStructure.FiniteIntermediateField K L)
    (hFG : F.toIntermediateField ≤ G.toIntermediateField)
    (B : Submodule F (F ⊗[K] E)) :
    Submodule.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K G L L E).toLinearMap
      ((Submodule.span G (TensorProduct.map (IntermediateField.inclusion hFG).toLinearMap
        (LinearMap.id : E →ₗ[K] E) '' (B : Set (F ⊗[K] E)))).baseChange L) =
    Submodule.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
      (B.baseChange L) := by
  have hB : Submodule.span F (B : Set (F ⊗[K] E)) = B := Submodule.span_eq B
  rw [← hB]
  simp only [Submodule.baseChange_span, Submodule.map_span, Set.image_image]
  rw [hB]
  congr 1
  apply Set.image_congr'
  intro z
  exact complexDescent_tensor_inclusion F G hFG z

/-- Transport an already produced family through an actual finite enlargement. -/
private theorem complexDescent_enlarge_subspaces {ι : Type v}
    (F : AdelicStructure.FiniteIntermediateField K L)
    (B : ι → Submodule F (F ⊗[K] E)) :
    ∃ G : AdelicStructure.FiniteIntermediateField K L, (∃ a : G, a ^ 2 = -1) ∧
      ∃ C : ι → Submodule G (G ⊗[K] E), ∀ i,
        Submodule.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K G L L E).toLinearMap
          ((C i).baseChange L) =
        Submodule.map (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap
          ((B i).baseChange L) := by
  obtain ⟨G, hFG, hroot⟩ := exists_complexFiniteStage_ge F
  let C := fun i => Submodule.span G
    (TensorProduct.map (IntermediateField.inclusion hFG).toLinearMap
      (LinearMap.id : E →ₗ[K] E) '' (B i : Set (F ⊗[K] E)))
  exact ⟨G, hroot, C, fun i => complexDescent_span_inclusion_image F G hFG (B i)⟩

variable [FiniteDimensional K E]

/-- A finite family of actual extended subspaces has one produced finite
complexifying field of definition, with literal images, ranks and inclusions. -/
theorem exists_complexFiniteStage_subspaces {ι : Type v} [Finite ι]
    (A : ι → Submodule L (L ⊗[K] E)) :
    ∃ G : AdelicStructure.FiniteIntermediateField K L, (∃ a : G, a ^ 2 = -1) ∧
      ∃ C : ι → Submodule G (G ⊗[K] E),
        (∀ i, Submodule.map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K G L L E).toLinearMap
          ((C i).baseChange L) = A i) ∧
        (∀ i, Module.finrank G (C i) = Module.finrank L (A i)) ∧
        (∀ i j, C i ≤ C j ↔ A i ≤ A j) := by
  obtain ⟨F, B, hB⟩ := exists_finiteStage_subspaces A
  obtain ⟨G, hroot, C, hC⟩ := complexDescent_enlarge_subspaces F B
  have he (i) : Submodule.map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K G L L E).toLinearMap
      ((C i).baseChange L) = A i := (hC i).trans (hB i)
  refine ⟨G, hroot, C, he, ?_, ?_⟩
  · intro i
    rw [← he i]
    exact (finrank_map_baseChange_cancelBaseChange G (C i)).symm
  · intro i j
    rw [← map_baseChange_cancelBaseChange_le_iff G (C i) (C j), he i, he j]

/-- An actual strict exhaustive flag descends to one produced finite
complexifying field, preserving literal terms, ranks and both endpoints. -/
theorem exists_complexFiniteStage_flag (n : ℕ)
    (A : Fin (n + 1) → Submodule L (L ⊗[K] E)) (hA : StrictMono A)
    (hbot : A 0 = ⊥) (htop : A (Fin.last n) = ⊤) :
    ∃ G : AdelicStructure.FiniteIntermediateField K L, (∃ a : G, a ^ 2 = -1) ∧
      ∃ C : Fin (n + 1) → Submodule G (G ⊗[K] E),
        (∀ i, Submodule.map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K G L L E).toLinearMap
          ((C i).baseChange L) = A i) ∧
        (∀ i, Module.finrank G (C i) = Module.finrank L (A i)) ∧
        StrictMono C ∧ C 0 = ⊥ ∧ C (Fin.last n) = ⊤ := by
  obtain ⟨F, B, hB, _, _, _, _⟩ := exists_finiteStage_flag n A hA hbot htop
  obtain ⟨G, hroot, C, hC⟩ := complexDescent_enlarge_subspaces F B
  have he (i) : Submodule.map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K G L L E).toLinearMap
      ((C i).baseChange L) = A i := (hC i).trans (hB i)
  refine ⟨G, hroot, C, he, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← he i]
    exact (finrank_map_baseChange_cancelBaseChange G (C i)).symm
  · intro i j hij
    apply lt_of_le_not_ge
    · apply (map_baseChange_cancelBaseChange_le_iff G (C i) (C j)).mp
      rw [he i, he j]
      exact (hA hij).le
    · intro hji
      have h := (map_baseChange_cancelBaseChange_le_iff G (C j) (C i)).mpr hji
      rw [he j, he i] at h
      exact (not_le_of_gt (hA hij)) h
  · apply Submodule.baseChange_injective (A := L)
    apply Submodule.map_injective_of_injective
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K G L L E).injective
    simp only [he 0, hbot, Submodule.baseChange_bot, Submodule.map_bot]
  · apply Submodule.baseChange_injective (A := L)
    apply Submodule.map_injective_of_injective
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K G L L E).injective
    rw [he (Fin.last n), htop, Submodule.baseChange_top, Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K G L L E).surjective).symm

end ArakelovGeometry

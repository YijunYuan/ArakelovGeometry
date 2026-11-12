/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerPlace
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.CommonNativeSubquotient

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.NativeSubquotientFiniteStage
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.ComplexDescent
import Mathlib.CategoryTheory.Category.Init

/-!
# One produced finite stage for all actual native flag factors

Original common density supplies all actual bundle and degree contexts.
Genuine flag descent chooses one field before any factor is considered;
canonical every-completed-vector subquotient isometries and mixed degrees
then transport to the literal prescribed target flag factors.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Rank, ordinary degree, and every completed norm are preserved by a native
subquotient comparison with its finite-stage model. -/
abbrev HasCommonNativeSubquotientComparison
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (P Q : Submodule F (F ⊗[K] E)) (A B : Submodule L (L ⊗[K] E)) : Prop :=
  Module.finrank L (B ⧸ A.comap B.subtype) = Module.finrank F (Q ⧸ P.comap Q.subtype) ∧
  V.CommonSubspaceQuotientDegreeEq (L := L) F P Q B (A.comap B.subtype) ∧
  ∃ e : (L ⊗[F] (Q ⧸ P.comap Q.subtype)) ≃ₗ[L] (B ⧸ A.comap B.subtype),
    ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (z : x.abv.Completion ⊗[L] (L ⊗[F] (Q ⧸ P.comap Q.subtype))),
      (((V.toNormFamily.scalarExtension (L := L)).restrict B).quotient
        (A.comap B.subtype)).norm (scalarExtensionTowerPlace x)
          (e.toLinearMap.baseChange x.abv.Completion z) =
        ((((V.toNormFamily.scalarExtension (L := F)).restrict Q).quotient
          (P.comap Q.subtype)).scalarExtension (L := L)).norm x z

private theorem hasCommonNativeSubquotientComparison_of_images
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q)
    (A B : Submodule L (L ⊗[K] E)) (hAB : A ≤ B)
    (hP : (P.baseChange L).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = A)
    (hQ : (Q.baseChange L).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = B)
    (hd : V.CommonNativeSubquotientDegreeEq (L := L) (hcount := hcount) F P Q) :
    V.HasCommonNativeSubquotientComparison (L := L) (hcount := hcount) F P Q A B := by
  obtain ⟨e, he, hr⟩ := V.toNormFamily.hasScalarExtensionSubquotientIsometry_of_images
    (L := L) F hi P Q hPQ A B hP hQ
  have hP' : (P.baseChange L).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap =
        (A.comap B.subtype).map B.subtype := by
    simpa only [Submodule.map_comap_subtype, inf_eq_right.mpr hAB] using hP
  exact ⟨hr, commonSubspaceQuotientDegreeEq_of_images V (hcount := hcount) F P Q B
    (A.comap B.subtype) hP' hQ hd, ⟨e, he⟩⟩

/-- One finite field preserves every flag factor's rank, ordinary degree, and
completed norms under a produced rational equivalence. -/
theorem exists_complexFiniteStage_nativeFlag_isometries_degrees_of_common_density
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (n : ℕ) (A : Fin (n + 1) → Submodule L (L ⊗[K] E))
    (hA : StrictMono A) (hbot : A 0 = ⊥) (htop : A (Fin.last n) = ⊤) :
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ C : Fin (n + 1) → Submodule F (F ⊗[K] E),
        (∀ i, ((C i).baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = A i) ∧
        (∀ i, Module.finrank F (C i) = Module.finrank L (A i)) ∧
        StrictMono C ∧ C 0 = ⊥ ∧ C (Fin.last n) = ⊤ ∧
        ∀ i : Fin n, V.HasCommonNativeSubquotientComparison (L := L) F
          (C i.castSucc) (C i.succ) (A i.castSucc) (A i.succ) := by
  obtain ⟨F, hi, C, hC, hr, hstrict, hzero, hlast⟩ :=
    exists_complexFiniteStage_flag n A hA hbot htop
  refine ⟨F, hi, C, hC, hr, hstrict, hzero, hlast, ?_⟩
  intro i
  exact hasCommonNativeSubquotientComparison_of_images V F hi
    (C i.castSucc) (C i.succ) (hstrict i.castSucc_lt_succ).le
    (A i.castSucc) (A i.succ) (hA i.castSucc_lt_succ).le (hC i.castSucc) (hC i.succ)
    (V.degree_nativeSubquotient_scalarExtension_finiteStage F hi
      (C i.castSucc) (C i.succ) (hstrict i.castSucc_lt_succ).le)

end ArakelovGeometry.AdelicVectorBundle

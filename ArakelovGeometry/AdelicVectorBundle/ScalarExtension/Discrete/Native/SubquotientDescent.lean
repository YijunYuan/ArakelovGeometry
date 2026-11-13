/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Degree.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.SubspaceQuotient

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Discrete.Native.SubquotientDegree
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.ComplexDescent
import Mathlib.CategoryTheory.Category.Init

/-!
# Produced finite stages for every actual native mixed degree

The genuine image of an arbitrary subspace of a native restriction descends
together with its parent. Its proved inverse-image identity transports the
actual finite-stage degree comparison to the prescribed quotient bundle.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
namespace AdelicVectorBundle
open NormFamily
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- The native quotient and its descended subquotient have equal ranks and degrees.

The degree uses the canonical quotient bundles, with determinant measurability and
normalization produced from the original adelic curve. -/
abbrev NativeSubquotientRankDegreeEq
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (P Q : Submodule F (F ⊗[K] V))
    (B : Submodule L (L ⊗[K] V)) (T : Submodule L B) : Prop :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  Module.finrank L (B ⧸ T) = Module.finrank F (Q ⧸ P.comap Q.subtype) ∧
    (V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase B T).degreeOfMeasurableDeterminant
      (hdet := V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase_determinant_isMeasurable
        B T)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
      (((V.scalarExtensionOfCountableDiscreteBase (L := F)).restrictOfMeasurableBase
        Q).quotientOfMeasurableBase
        (P.comap Q.subtype)).degree
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩)

private theorem nativeSubquotientRankDegreeEq_of_images
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (P Q : Submodule F (F ⊗[K] V)) (hPQ : P ≤ Q)
    (A B : Submodule L (L ⊗[K] V))
    (hP : (P.baseChange L).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L V).toLinearMap = A)
    (hQ : (Q.baseChange L).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L V).toLinearMap = B)
    (hd : V.NativeSubquotientDegreeEq (L := L) F P Q) :
    V.NativeSubquotientRankDegreeEq F P Q B (A.comap B.subtype) := by
  subst B
  subst A
  constructor
  · exact (finiteStageSubquotientEquiv (L := L) F P Q hPQ).finrank_eq.symm.trans
      Module.finrank_baseChange
  · exact hd

/-- Every actual native mixed quotient has a produced complexifying finite
stage with literal endpoint images, its actual rank, and its actual degree.
No target regularity or finite-stage certificate is required. -/
theorem exists_complexFiniteStage_nativeSubquotient_degree
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (B : Submodule L (L ⊗[K] V)) (T : Submodule L B) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ P Q : Submodule F (F ⊗[K] V), P ≤ Q ∧
        (P.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L V).toLinearMap =
            T.map B.subtype ∧
        (Q.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L V).toLinearMap = B ∧
        V.NativeSubquotientRankDegreeEq F P Q B T := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let A := T.map B.subtype
  have hAB : A ≤ B := B.map_subtype_le T
  have hT : A.comap B.subtype = T := by
    change (T.map B.subtype).comap B.subtype = T
    rw [Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
  obtain ⟨F, hi, P, Q, hPQ, hP, hQ, _, _, _⟩ :=
    V.toNormFamily.exists_complexFiniteStage_subquotient_isometry A B hAB
  refine ⟨F, hi, P, Q, hPQ, hP, hQ, ?_⟩
  have hd := V.degree_nativeSubquotientOfCountableDiscreteBase_finiteStage F hi P Q hPQ
  have h := nativeSubquotientRankDegreeEq_of_images V F P Q hPQ A B hP hQ hd
  exact Eq.mp (congrArg (fun T' : Submodule L B =>
    V.NativeSubquotientRankDegreeEq F P Q B T') hT) h

/-- A single produced complexifying finite stage preserves every actual mixed
factor degree and rank of a prescribed full strict flag, including length zero. -/
theorem exists_complexFiniteStage_nativeFlag_factor_degrees
    (V : AdelicVectorBundle S)
    [hN : S.IsArchimedeanNormalized]
    (n : ℕ) (A : Fin (n + 1) → Submodule L (L ⊗[K] V))
    (hA : StrictMono A) (hbot : A 0 = ⊥) (htop : A (Fin.last n) = ⊤) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ C : Fin (n + 1) → Submodule F (F ⊗[K] V),
        (∀ i, ((C i).baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L V).toLinearMap = A i) ∧
        (∀ i, Module.finrank F (C i) = Module.finrank L (A i)) ∧
        StrictMono C ∧ C 0 = ⊥ ∧ C (Fin.last n) = ⊤ ∧
        ∀ i : Fin n,
          V.NativeSubquotientRankDegreeEq F (C i.castSucc) (C i.succ)
            (A i.succ) ((A i.castSucc).comap (A i.succ).subtype) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  obtain ⟨F, hi, C, hC, hr, hstrict, hzero, hlast⟩ :=
    exists_complexFiniteStage_flag n A hA hbot htop
  refine ⟨F, hi, C, hC, hr, hstrict, hzero, hlast, ?_⟩
  intro i
  have hPQ : C i.castSucc ≤ C i.succ := (hstrict i.castSucc_lt_succ).le
  exact nativeSubquotientRankDegreeEq_of_images V F (C i.castSucc) (C i.succ) hPQ
    (A i.castSucc) (A i.succ) (hC i.castSucc) (hC i.succ)
    (V.degree_nativeSubquotientOfCountableDiscreteBase_finiteStage F hi
      (C i.castSucc) (C i.succ) hPQ)

end AdelicVectorBundle
end ArakelovGeometry

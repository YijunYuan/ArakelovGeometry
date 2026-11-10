/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteNativeSubquotientDegree

/-!
# Produced finite stages for every actual native mixed degree

The genuine image of an arbitrary subspace of a native restriction descends
together with its parent. Its proved inverse-image identity transports the
actual finite-stage degree comparison to the prescribed quotient bundle.
-/

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

/-- Every actual native mixed quotient has a produced complexifying finite
stage with literal endpoint images, its actual rank, and its actual degree.
No target regularity or finite-stage certificate is required. -/
theorem exists_complexFiniteStage_nativeSubquotient_degree
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (B : Submodule L (L ⊗[K] E)) (T : Submodule L B) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ P Q : Submodule F (F ⊗[K] E), P ≤ Q ∧
        (P.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap =
            T.map B.subtype ∧
        (Q.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = B ∧
        Module.finrank L (B ⧸ T) = Module.finrank F (Q ⧸ P.comap Q.subtype) ∧
        (let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
         let : Countable (S.algebraicExtension F).Ω :=
           AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
         let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
           AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
             (S := S) (L := F)
         let R := V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase hN B T
         R.degreeOfMeasurableDeterminant
             (scalarExtension_restrict_quotient_determinant_isMeasurable_of_countable_discrete
               V.toNormFamily hN B T)
             (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
           (((V.scalarExtensionOfCountableDiscreteBase (L := F) hN).restrictOfMeasurableBase
             Q (Or.inl inferInstance)).quotientOfMeasurableBase
               (P.comap Q.subtype) (Or.inl inferInstance)).degree (Or.inl inferInstance)
             (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN)) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let A := T.map B.subtype
  have hAB : A ≤ B := B.map_subtype_le T
  have hT : A.comap B.subtype = T := by
    change (T.map B.subtype).comap B.subtype = T
    rw [Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
  obtain ⟨F, hi, P, Q, hPQ, hP, hQ, _, _, hr⟩ :=
    V.toNormFamily.exists_complexFiniteStage_subquotient_isometry hN A B hAB
  refine ⟨F, hi, P, Q, hPQ, hP, hQ, ?_, ?_⟩
  · exact Eq.mp (congrArg (fun C : Submodule L B =>
      Module.finrank L (B ⧸ C) = Module.finrank F (Q ⧸ P.comap Q.subtype)) hT) hr
  · let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let : Countable (S.algebraicExtension F).Ω :=
      AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
    let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
      AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
        (S := S) (L := F)
    let d (P' Q' : Submodule L (L ⊗[K] E)) : ℝ :=
      (V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase hN Q'
        (P'.comap Q'.subtype)).degreeOfMeasurableDeterminant
          (scalarExtension_restrict_quotient_determinant_isMeasurable_of_countable_discrete
            V.toNormFamily hN Q' (P'.comap Q'.subtype))
          (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)
    have hd := V.degree_nativeSubquotientOfCountableDiscreteBase_finiteStage hN F hi P Q hPQ
    dsimp only at hd
    have he := congrArg₂ d hP hQ
    have ht := congrArg (fun C : Submodule L B =>
      let R := V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase hN B C
      R.degreeOfMeasurableDeterminant
          (scalarExtension_restrict_quotient_determinant_isMeasurable_of_countable_discrete
            V.toNormFamily hN B C)
          (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)) hT
    exact ht.symm.trans (he.symm.trans hd)

end AdelicVectorBundle
end ArakelovGeometry

namespace ArakelovGeometry.AdelicVectorBundle
open NormFamily
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- A single produced complexifying finite stage preserves every actual mixed
factor degree and rank of a prescribed full strict flag, including length zero. -/
theorem exists_complexFiniteStage_nativeFlag_factor_degrees
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (n : ℕ) (A : Fin (n + 1) → Submodule L (L ⊗[K] E))
    (hA : StrictMono A) (hbot : A 0 = ⊥) (htop : A (Fin.last n) = ⊤) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ C : Fin (n + 1) → Submodule F (F ⊗[K] E),
        (∀ i, ((C i).baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = A i) ∧
        (∀ i, Module.finrank F (C i) = Module.finrank L (A i)) ∧
        StrictMono C ∧ C 0 = ⊥ ∧ C (Fin.last n) = ⊤ ∧
        ∀ i : Fin n,
          Module.finrank L (A i.succ ⧸ (A i.castSucc).comap (A i.succ).subtype) =
            Module.finrank F (C i.succ ⧸ (C i.castSucc).comap (C i.succ).subtype) ∧
          (let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
           let : Countable (S.algebraicExtension F).Ω :=
             AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional
               (S := S) (L := F)
           let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
             AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
               (S := S) (L := F)
           let R := V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase hN
             (A i.succ) ((A i.castSucc).comap (A i.succ).subtype)
           R.degreeOfMeasurableDeterminant
             (scalarExtension_restrict_quotient_determinant_isMeasurable_of_countable_discrete
               V.toNormFamily hN (A i.succ) ((A i.castSucc).comap (A i.succ).subtype))
             (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
             (((V.scalarExtensionOfCountableDiscreteBase (L := F) hN).restrictOfMeasurableBase
               (C i.succ) (Or.inl inferInstance)).quotientOfMeasurableBase
                 ((C i.castSucc).comap (C i.succ).subtype) (Or.inl inferInstance)).degree
               (Or.inl inferInstance)
               (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN)) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  obtain ⟨F, hi, C, hC, hr, hstrict, hzero, hlast⟩ :=
    exists_complexFiniteStage_flag n A hA hbot htop
  refine ⟨F, hi, C, hC, hr, hstrict, hzero, hlast, ?_⟩
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let : Countable (S.algebraicExtension F).Ω :=
    AdelicStructure.ParameterSpaceExtension.countable_of_finiteDimensional (S := S) (L := F)
  let : DiscreteMeasurableSpace (S.algebraicExtension F).Ω :=
    AdelicStructure.discreteMeasurableSpace_algebraicExtension_of_finiteDimensional
      (S := S) (L := F)
  intro i
  have hPQ : C i.castSucc ≤ C i.succ := (hstrict i.castSucc_lt_succ).le
  let r (P Q : Submodule L (L ⊗[K] E)) := Module.finrank L (Q ⧸ P.comap Q.subtype)
  let d (P Q : Submodule L (L ⊗[K] E)) : ℝ :=
    (V.scalarExtensionSubspaceQuotientOfCountableDiscreteBase hN Q
      (P.comap Q.subtype)).degreeOfMeasurableDeterminant
        (scalarExtension_restrict_quotient_determinant_isMeasurable_of_countable_discrete
          V.toNormFamily hN Q (P.comap Q.subtype))
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)
  have heRank := congrArg₂ r (hC i.castSucc) (hC i.succ)
  have heDegree := congrArg₂ d (hC i.castSucc) (hC i.succ)
  constructor
  · exact heRank.symm.trans
      ((finiteStageSubquotientEquiv F (C i.castSucc) (C i.succ) hPQ).finrank_eq.symm.trans
        Module.finrank_baseChange)
  · have hd := V.degree_nativeSubquotientOfCountableDiscreteBase_finiteStage hN F hi
      (C i.castSucc) (C i.succ) hPQ
    dsimp only at hd
    exact heDegree.symm.trans hd

end ArakelovGeometry.AdelicVectorBundle

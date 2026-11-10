/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionNativeSubquotientFiniteStage
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionSubspaceDegree

/-!
# Actual mixed subquotients with produced common density

Original common density produces every target density context. The existing
canonical bundle operations retain the literal native completed restriction
and quotient norms. Actual all-completed finite-stage transport then preserves
their ordinary determinant degrees, without original ultrametricity.
-/

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Original common density produces actual primal, completed dual and
determinant measurability and domination for every literal native B/T. -/
theorem scalarExtension_nativeSubquotient_regular_of_common_density
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (B : Submodule L (L ⊗[K] E)) (T : Submodule L B) :
    let θ := ((V.toNormFamily.scalarExtension (L := L)).restrict B).quotient T
    θ.IsMeasurable ∧ θ.dual.IsMeasurable ∧ θ.IsDominated ∧
      θ.determinant.IsMeasurable := by
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let R := ((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase
    B (Or.inr hL)).quotientOfMeasurableBase T (Or.inr hL)
  change R.toNormFamily.IsMeasurable ∧ R.toNormFamily.dual.IsMeasurable ∧
    R.toNormFamily.IsDominated ∧ R.toNormFamily.determinant.IsMeasurable
  exact ⟨R.isMeasurable, R.dual_isMeasurable, R.isDominated,
    R.isMeasurable.determinant_of_discrete_or_countable (Or.inr hL)⟩

/-- Genuine native mixed degrees at a complexifying finite stage. All source,
target and tower density contexts are produced from original common density. -/
theorem degree_nativeSubquotient_scalarExtension_finiteStage [S.IsProper]
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let hF := hcount.algebraicExtension_of_finiteDimensional (L := F)
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (P.baseChange L).map c.toLinearMap
    let B := (Q.baseChange L).map c.toLinearMap
    (((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase
      B (Or.inr hL)).quotientOfMeasurableBase (A.comap B.subtype) (Or.inr hL)).degree
        (Or.inr hL) (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
      (((V.scalarExtension (L := F) hcount hN).restrictOfMeasurableBase
        Q (Or.inr hF)).quotientOfMeasurableBase (P.comap Q.subtype) (Or.inr hF)).degree
          (Or.inr hF) (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let hF := hcount.algebraicExtension_of_finiteDimensional (L := F)
  let hT := hF.algebraicExtension_of_isAlgClosed (L := L)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let hFN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN
  let hTN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hFN
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
  let A := (P.baseChange L).map c.toLinearMap
  let B := (Q.baseChange L).map c.toLinearMap
  let W₀ : AdelicVectorBundle (S.algebraicExtension F) (Q ⧸ P.comap Q.subtype) :=
    ((V.scalarExtension (L := F) hcount hN).restrictOfMeasurableBase
      Q (Or.inr hF)).quotientOfMeasurableBase (P.comap Q.subtype) (Or.inr hF)
  let R : AdelicVectorBundle (S.algebraicExtension L) (B ⧸ A.comap B.subtype) :=
    ((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase
      B (Or.inr hL)).quotientOfMeasurableBase (A.comap B.subtype) (Or.inr hL)
  let W := W₀.scalarExtension (L := L) hF hFN
  let T := R.towerPullback F.toIntermediateField
  change R.degree (Or.inr hL) hLN = W₀.degree (Or.inr hF) hFN
  have he : W.degree (Or.inr hT) hTN = T.degree (Or.inr hT) hTN :=
    W.degree_eq_of_completed_isometry T (finiteStageSubquotientEquiv F P Q hPQ)
      (Or.inr hT) hTN (by
        intro x z
        exact V.toNormFamily.scalarExtension_subquotient_finiteStage_norm_eq hN F hi P Q hPQ x z)
  have ht : T.degree (Or.inr hT) hTN = R.degree (Or.inr hL) hLN :=
    R.degree_towerPullback F.toIntermediateField (Or.inr hL) (Or.inr hT) hLN hTN
  exact ht.symm.trans (he.symm.trans (W₀.degree_scalarExtension_of_isAlgClosed hF hFN))

/-- An arbitrary actual native B/T has a produced complexifying finite stage,
with literal endpoint images, genuine quotient rank and actual ordinary degree. -/
theorem exists_complexFiniteStage_nativeSubquotient_degree_of_common_density [S.IsProper]
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (B : Submodule L (L ⊗[K] E)) (T : Submodule L B) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ P Q : Submodule F (F ⊗[K] E), P ≤ Q ∧
        (P.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap =
            T.map B.subtype ∧
        (Q.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = B ∧
        Module.finrank L (B ⧸ T) = Module.finrank F (Q ⧸ P.comap Q.subtype) ∧
        (let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
         let hF := hcount.algebraicExtension_of_finiteDimensional (L := F)
         (((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase
           B (Or.inr hL)).quotientOfMeasurableBase T (Or.inr hL)).degree (Or.inr hL)
             (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
           (((V.scalarExtension (L := F) hcount hN).restrictOfMeasurableBase
             Q (Or.inr hF)).quotientOfMeasurableBase (P.comap Q.subtype) (Or.inr hF)).degree
               (Or.inr hF)
               (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN)) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
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
    let d (P' Q' : Submodule L (L ⊗[K] E)) : ℝ :=
      (((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase
        Q' (Or.inr hL)).quotientOfMeasurableBase (P'.comap Q'.subtype) (Or.inr hL)).degree
          (Or.inr hL) (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)
    have hd := V.degree_nativeSubquotient_scalarExtension_finiteStage hcount hN F hi P Q hPQ
    dsimp only at hd
    have he := congrArg₂ d hP hQ
    have ht := congrArg (fun C : Submodule L B =>
      (((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase
        B (Or.inr hL)).quotientOfMeasurableBase C (Or.inr hL)).degree (Or.inr hL)
          (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)) hT
    exact ht.symm.trans (he.symm.trans hd)

end ArakelovGeometry.AdelicVectorBundle

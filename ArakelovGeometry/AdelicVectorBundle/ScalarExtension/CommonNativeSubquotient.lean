/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Algebraic.ClosureApproximation
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Bundle

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.NativeSubquotientFiniteStage
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.Degree
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual mixed subquotients with produced common density

Original common density produces every target density context. The existing
canonical bundle operations retain the literal native completed restriction
and quotient norms. Actual all-completed finite-stage transport then preserves
their ordinary determinant degrees, without original ultrametricity.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u wL wE
variable {K : Type u} [Field K] {S : AdelicStructure K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Original common density produces actual primal, completed dual and
determinant measurability and domination for every literal native B/T. -/
theorem scalarExtension_nativeSubquotient_regular_of_common_density
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (B : Submodule L (L ⊗[K] V)) (T : Submodule L B) :
    let θ := ((V.toNormFamily.scalarExtension (L := L)).restrict B).quotient T
    θ.IsMeasurable ∧ θ.dual.IsMeasurable ∧ θ.IsDominated ∧
      θ.determinant.IsMeasurable := by
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let R := ((V.scalarExtension (L := L)).restrictOfMeasurableBase
    B).quotientOfMeasurableBase T
  change R.toNormFamily.IsMeasurable ∧ R.toNormFamily.dual.IsMeasurable ∧
    R.toNormFamily.IsDominated ∧ R.toNormFamily.determinant.IsMeasurable
  exact ⟨R.isMeasurable, R.dual_isMeasurable, R.isDominated,
    R.isMeasurable.determinant_of_discrete_or_countable⟩

private theorem degree_eq_of_scalarExtension_tower_isometry [S.IsProper]
    (F : IntermediateField K L)
    (W₀ : AdelicVectorBundle (S.algebraicExtension F))
    (R : AdelicVectorBundle (S.algebraicExtension L))
    (e : (L ⊗[F] W₀) ≃ₗ[L] R)
    (hF : (S.algebraicExtension F).HasCommonCountableDenseSubfield)
    (hL : (S.algebraicExtension L).HasCommonCountableDenseSubfield)
    [hFN : (S.algebraicExtension F).IsArchimedeanNormalized]
    [hLN : (S.algebraicExtension L).IsArchimedeanNormalized]
    (he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (z : x.abv.Completion ⊗[L] (L ⊗[F] W₀)), R.toNormFamily.norm (scalarExtensionTowerPlace x)
        (e.toLinearMap.baseChange x.abv.Completion z) =
          (W₀.toNormFamily.scalarExtension (L := L)).norm x z) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    R.degree (hN := ⟨hLN⟩) = W₀.degree (hN := ⟨hFN⟩) := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  exact (degree_eq_of_tower_completed_isometry F
    (W₀.scalarExtension (L := L) (hS := hF) (hN := ⟨hFN⟩)) R e
    (hT := ⟨(Or.inr (hF.algebraicExtension_of_isAlgClosed (L := L)))⟩) (hND := ⟨hLN⟩)
    (hNT := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L)
        (hS := ⟨hFN⟩))⟩) he).trans
      (W₀.degree_scalarExtension_of_isAlgClosed (hcount := hF) (hN := ⟨hFN⟩))

universe wF

/-- Equality of the degree of a native quotient `B / T` and that of a finite-stage
subquotient `Q / P`, with the induced density and normalization contexts. -/
abbrev CommonSubspaceQuotientDegreeEq [S.IsProper]
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (F : Type wF) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (P Q : Submodule F (F ⊗[K] V))
    (B : Submodule L (L ⊗[K] V)) (T : Submodule L B) : Prop :=
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
    let _ := hcount.algebraicExtension_of_isAlgClosed (L := L)
    let _ := hcount.algebraicExtension_of_finiteDimensional (L := F)
    (((V.scalarExtension (L := L)).restrictOfMeasurableBase
      B).quotientOfMeasurableBase T).degree
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
      (((V.scalarExtension (L := F)).restrictOfMeasurableBase
        Q).quotientOfMeasurableBase (P.comap Q.subtype)).degree
          (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩)


/-- Equality between the native degree of a scalar-extended subquotient and its
finite-stage degree, with density and normalization induced from the original curve. -/
abbrev CommonNativeSubquotientDegreeEq [S.IsProper]
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (F : Type wF) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (P Q : Submodule F (F ⊗[K] V)) : Prop :=
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L V
  let A := (P.baseChange L).map c.toLinearMap
  let B := (Q.baseChange L).map c.toLinearMap
  V.CommonSubspaceQuotientDegreeEq (L := L) F P Q B (A.comap B.subtype)

private theorem common_nativeSubquotient_canonical_degree [S.IsProper]
    (V : AdelicVectorBundle.{wE} S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (F : Type wF) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (hd : ∀
      (W₀ : AdelicVectorBundle.{max wF wE} (S.algebraicExtension F))
      (R : AdelicVectorBundle.{max wL wE} (S.algebraicExtension L)) (e : (L ⊗[F] W₀) ≃ₗ[L] R)
      (_he : ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
        (z : x.abv.Completion ⊗[L] (L ⊗[F] W₀)), R.toNormFamily.norm (scalarExtensionTowerPlace x)
          (e.toLinearMap.baseChange x.abv.Completion z) =
            (W₀.toNormFamily.scalarExtension (L := L)).norm x z),
      let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
      let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
      R.degree (hS := ⟨(Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))⟩)
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
      W₀.degree (hS := ⟨(Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := F)))⟩)
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F))⟩))
    (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] V)) (hPQ : P ≤ Q) :
    V.CommonNativeSubquotientDegreeEq (L := L) (hcount := hcount) F P Q := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let := AdelicStructure.Algebraic.isProper_algebraicExtension (S.algebraicExtension F) L
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  let hF := hcount.algebraicExtension_of_finiteDimensional (L := F)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
  let hFN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := F)
  let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L V
  let A := (P.baseChange L).map c.toLinearMap
  let B := (Q.baseChange L).map c.toLinearMap
  let W₀ : AdelicVectorBundle (S.algebraicExtension F) :=
    ((V.scalarExtension (L := F) (hS := hcount)).restrictOfMeasurableBase
      Q).quotientOfMeasurableBase (P.comap Q.subtype)
  let R : AdelicVectorBundle (S.algebraicExtension L) :=
    ((V.scalarExtension (L := L) (hS := hcount)).restrictOfMeasurableBase
      B).quotientOfMeasurableBase (A.comap B.subtype)
  change R.degree (hN := ⟨hLN⟩) = W₀.degree (hN := ⟨hFN⟩)
  obtain ⟨e, he, _⟩ := V.toNormFamily.hasScalarExtensionSubquotientIsometry_of_images
    (L := L) F hi P Q hPQ A B rfl rfl
  apply hd W₀ R e
  intro x z
  simpa only [W₀, R, quotientOfMeasurableBase_toNormFamily,
    restrictOfMeasurableBase_toNormFamily, scalarExtension_toNormFamily] using he x z


/-- Genuine native mixed degrees at a complexifying finite stage. All source,
target and tower density contexts are produced from original common density. -/
theorem degree_nativeSubquotient_scalarExtension_finiteStage [S.IsProper]
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (F : AdelicStructure.FiniteIntermediateField K L) (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] V)) (hPQ : P ≤ Q) :
    V.CommonNativeSubquotientDegreeEq (L := L) F P Q := by
  refine common_nativeSubquotient_canonical_degree V F ?_ hi P Q hPQ
  intro W₀ R e he
  exact degree_eq_of_scalarExtension_tower_isometry F.toIntermediateField W₀ R e
    (hcount.algebraicExtension_of_finiteDimensional (L := F))
    (hcount.algebraicExtension_of_isAlgClosed (L := L))
    he

/-- Exact endpoint images transport the canonical finite-stage degree identity
to the prescribed native quotient. -/
theorem commonSubspaceQuotientDegreeEq_of_images [S.IsProper]
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (F : Type wF) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] [FiniteDimensional K F]
    (P Q : Submodule F (F ⊗[K] V))
    (B : Submodule L (L ⊗[K] V)) (T : Submodule L B)
    (hP : (P.baseChange L).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L V).toLinearMap =
        T.map B.subtype)
    (hQ : (Q.baseChange L).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L V).toLinearMap = B)
    (hd : V.CommonNativeSubquotientDegreeEq (L := L) F P Q) :
    V.CommonSubspaceQuotientDegreeEq (L := L) F P Q B T := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  have hT : (T.map B.subtype).comap B.subtype = T := by
    rw [Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
  let d (P' Q' : Submodule L (L ⊗[K] V)) : ℝ :=
    (((V.scalarExtension (L := L)).restrictOfMeasurableBase
      Q').quotientOfMeasurableBase (P'.comap Q'.subtype)).degree
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩)
  dsimp only [CommonNativeSubquotientDegreeEq, CommonSubspaceQuotientDegreeEq] at hd ⊢
  have he := congrArg₂ d hP hQ
  have ht := congrArg (fun C : Submodule L B =>
    (((V.scalarExtension (L := L)).restrictOfMeasurableBase
      B).quotientOfMeasurableBase C).degree
        (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩)) hT
  exact ht.symm.trans (he.symm.trans hd)

/-- An arbitrary actual native B/T has a produced complexifying finite stage,
with literal endpoint images, genuine quotient rank and actual ordinary degree. -/
theorem exists_complexFiniteStage_nativeSubquotient_degree_of_common_density [S.IsProper]
    (V : AdelicVectorBundle S) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    (B : Submodule L (L ⊗[K] V)) (T : Submodule L B) :
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ P Q : Submodule F (F ⊗[K] V), P ≤ Q ∧
        (P.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L V).toLinearMap =
            T.map B.subtype ∧
        (Q.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L V).toLinearMap = B ∧
        Module.finrank L (B ⧸ T) = Module.finrank F (Q ⧸ P.comap Q.subtype) ∧
        V.CommonSubspaceQuotientDegreeEq (L := L) F P Q B T := by
  let A := T.map B.subtype
  have hAB : A ≤ B := B.map_subtype_le T
  have hT : A.comap B.subtype = T := by
    change (T.map B.subtype).comap B.subtype = T
    rw [Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
  obtain ⟨F, hi, P, Q, hPQ, hP, hQ, _, _, hr⟩ :=
    V.toNormFamily.exists_complexFiniteStage_subquotient_isometry A B hAB
  refine ⟨F, hi, P, Q, hPQ, hP, hQ, ?_, ?_⟩
  · exact Eq.mp (congrArg (fun C : Submodule L B =>
      Module.finrank L (B ⧸ C) = Module.finrank F (Q ⧸ P.comap Q.subtype)) hT) hr
  · exact commonSubspaceQuotientDegreeEq_of_images V F P Q B T hP hQ
      (V.degree_nativeSubquotient_scalarExtension_finiteStage F hi P Q hPQ)

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionCommonNativeSubquotient

/-!
# One produced finite stage for all actual native flag factors

Original common density supplies all actual bundle and degree contexts.
Genuine flag descent chooses one field before any factor is considered;
canonical every-completed-vector subquotient isometries and mixed degrees
then transport to the literal prescribed target flag factors.
-/

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- A single produced finite field preserves every genuine flag factor's rank,
ordinary degree and ALL completed norms under an actual produced equivalence. -/
theorem exists_complexFiniteStage_nativeFlag_isometries_degrees_of_common_density
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (n : ℕ) (A : Fin (n + 1) → Submodule L (L ⊗[K] E))
    (hA : StrictMono A) (hbot : A 0 = ⊥) (htop : A (Fin.last n) = ⊤) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
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
           let hF := hcount.algebraicExtension_of_finiteDimensional (L := F)
           (((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase
             (A i.succ) (Or.inr hL)).quotientOfMeasurableBase
               ((A i.castSucc).comap (A i.succ).subtype) (Or.inr hL)).degree
             (Or.inr hL)
             (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
             (((V.scalarExtension (L := F) hcount hN).restrictOfMeasurableBase
               (C i.succ) (Or.inr hF)).quotientOfMeasurableBase
                 ((C i.castSucc).comap (C i.succ).subtype) (Or.inr hF)).degree
               (Or.inr hF)
               (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := F) hN)) ∧
          ∃ e : (L ⊗[F] (C i.succ ⧸ (C i.castSucc).comap (C i.succ).subtype)) ≃ₗ[L]
            (A i.succ ⧸ (A i.castSucc).comap (A i.succ).subtype),
            ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
              (z : x.abv.Completion ⊗[L]
                (L ⊗[F] (C i.succ ⧸ (C i.castSucc).comap (C i.succ).subtype))),
              (((V.toNormFamily.scalarExtension (L := L)).restrict (A i.succ)).quotient
                ((A i.castSucc).comap (A i.succ).subtype)).norm (scalarExtensionTowerPlace x)
                  (e.toLinearMap.baseChange x.abv.Completion z) =
                ((((V.toNormFamily.scalarExtension (L := F)).restrict (C i.succ)).quotient
                  ((C i.castSucc).comap (C i.succ).subtype)).scalarExtension
                    (L := L)).norm x z := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let hL := hcount.algebraicExtension_of_isAlgClosed (L := L)
  obtain ⟨F, hi, C, hC, hr, hstrict, hzero, hlast⟩ :=
    exists_complexFiniteStage_flag n A hA hbot htop
  refine ⟨F, hi, C, hC, hr, hstrict, hzero, hlast, ?_⟩
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S F
  intro i
  have hPQ : C i.castSucc ≤ C i.succ := (hstrict i.castSucc_lt_succ).le
  let r (P Q : Submodule L (L ⊗[K] E)) := Module.finrank L (Q ⧸ P.comap Q.subtype)
  let d (P Q : Submodule L (L ⊗[K] E)) : ℝ :=
    (((V.scalarExtension (L := L) hcount hN).restrictOfMeasurableBase
      Q (Or.inr hL)).quotientOfMeasurableBase (P.comap Q.subtype) (Or.inr hL)).degree
        (Or.inr hL) (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)
  have heRank := congrArg₂ r (hC i.castSucc) (hC i.succ)
  have heDegree := congrArg₂ d (hC i.castSucc) (hC i.succ)
  refine ⟨heRank.symm.trans
    ((finiteStageSubquotientEquiv F (C i.castSucc) (C i.succ) hPQ).finrank_eq.symm.trans
      Module.finrank_baseChange), ?_, ?_⟩
  · have hd := V.degree_nativeSubquotient_scalarExtension_finiteStage hcount hN F hi
      (C i.castSucc) (C i.succ) hPQ
    dsimp only at hd
    exact heDegree.symm.trans hd
  · let I (P Q : Submodule L (L ⊗[K] E)) : Prop :=
      ∃ e : (L ⊗[F] (C i.succ ⧸ (C i.castSucc).comap (C i.succ).subtype)) ≃ₗ[L]
          (Q ⧸ P.comap Q.subtype),
        ∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
          (z : x.abv.Completion ⊗[L]
            (L ⊗[F] (C i.succ ⧸ (C i.castSucc).comap (C i.succ).subtype))),
          (((V.toNormFamily.scalarExtension (L := L)).restrict Q).quotient
            (P.comap Q.subtype)).norm (scalarExtensionTowerPlace x)
              (e.toLinearMap.baseChange x.abv.Completion z) =
            ((((V.toNormFamily.scalarExtension (L := F)).restrict (C i.succ)).quotient
              ((C i.castSucc).comap (C i.succ).subtype)).scalarExtension (L := L)).norm x z
    have hI := congrArg₂ I (hC i.castSucc) (hC i.succ)
    apply Eq.mp hI
    refine ⟨finiteStageSubquotientEquiv F (C i.castSucc) (C i.succ) hPQ, ?_⟩
    intro x z
    exact V.toNormFamily.scalarExtension_subquotient_finiteStage_norm_eq hN F hi
      (C i.castSucc) (C i.succ) hPQ x z

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.DeterminantDegree

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Galois.DestabilizerBaseChange
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Galois.MaximalSlope
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Galois.Semistability
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Quotient
import Mathlib.CategoryTheory.Category.Init

/-!
# The actual finite Galois Hermitian HN flag under base change

Every actual quotient's largest destabilizer transports through the genuine
completed quotient isometry. The canonical recursive HN construction therefore
commutes with base change, including its zero and terminal endpoints.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section

namespace Submodule

variable {K L E F : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- Images of actual rational subspaces commute with scalar extension. -/
theorem map_baseChange (U : Submodule K E) (f : E →ₗ[K] F) :
    (U.baseChange L).map (f.baseChange L) = (U.map f).baseChange L := by
  let g := f.comp U.subtype
  have hg : g.range = U.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hr : (g.baseChange L).range = g.range.baseChange L := by
    change (g.baseChange L).range = (g.range.subtype.baseChange L).range
    conv_lhs => rw [show g = g.range.subtype.comp g.rangeRestrict from rfl,
      LinearMap.baseChange_comp]
    exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
      (LinearMap.baseChange_surjective L g.surjective_rangeRestrict))
  change (U.subtype.baseChange L).range.map (f.baseChange L) = _
  rw [← LinearMap.range_comp, ← LinearMap.baseChange_comp]
  exact hr.trans (congrArg (fun T : Submodule K F ↦ T.baseChange L) hg)

end Submodule

namespace ArakelovGeometry.AdelicVectorBundle

variable {K : Type*} [Field K] {S : AdelicStructure K} [S.IsProper]
  {E F : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- A completed isometry maps the actual largest destabilizer into the
target's actual largest destabilizer by its genuine restricted slope. -/
theorem map_destabilizingSubspace_le_of_completed_isometry
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
    (hr : 0 < Module.finrank K E) (hrF : 0 < Module.finrank K F)
    (he : ∀ ω z, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion z) = V.toNormFamily.norm ω z) :
    (V.destabilizingSubspace hr).map e.toLinearMap ≤
      W.destabilizingSubspace hrF := by
  let D := V.destabilizingSubspace hr
  have hp : 0 < Module.finrank K (D.map e.toLinearMap) := by
    rw [← (e.submoduleMap D).finrank_eq]
    exact V.destabilizingSubspace_finrank_pos hr
  have hm : (V.restrictOfMeasurableBase D).slope =
      (W.restrictOfMeasurableBase (D.map e.toLinearMap)).slope := by
    apply slope_eq_of_completed_isometry _ _ (e.submoduleMap D)
    intro ω z
    exact V.toNormFamily.restrict_map_equiv_norm_eq W.toNormFamily e D ω (he ω) z
  apply W.le_destabilizingSubspace_of_slope_eq_maximalSlope hrF _ hp
  exact ((congrArg (fun x : ℝ ↦ (x : EReal)) hm.symm).trans
    (V.slope_destabilizingSubspace_eq_maximalSlope hr)).trans
      (V.maximalSlope_eq_of_completed_isometry W e he)

/-- Actual completed isometries identify the actual largest destabilizers. -/
theorem map_destabilizingSubspace_eq_of_completed_isometry
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
    (hr : 0 < Module.finrank K E) (hrF : 0 < Module.finrank K F)
    (he : ∀ ω z, W.toNormFamily.norm ω
      (e.toLinearMap.baseChange (S.ϕ ω).Completion z) = V.toNormFamily.norm ω z) :
    (V.destabilizingSubspace hr).map e.toLinearMap =
      W.destabilizingSubspace hrF := by
  apply le_antisymm
    (V.map_destabilizingSubspace_le_of_completed_isometry W e hr hrF he)
  have hs : ∀ ω z, V.toNormFamily.norm ω
      (e.symm.toLinearMap.baseChange (S.ϕ ω).Completion z) = W.toNormFamily.norm ω z := by
    intro ω z
    let eω := e.baseChange K (S.ϕ ω).Completion E F
    change V.toNormFamily.norm ω (eω.symm z) = W.toNormFamily.norm ω z
    have h := he ω (eω.symm z)
    change W.toNormFamily.norm ω (eω (eω.symm z)) = V.toNormFamily.norm ω (eω.symm z) at h
    simpa only [LinearEquiv.apply_symm_apply] using h.symm
  have h := Submodule.map_mono (f := e.toLinearMap)
    (W.map_destabilizingSubspace_le_of_completed_isometry V e.symm
       hrF hr hs)
  simpa only [← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id] using h

section ScalarExtension

variable {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance hermitianGaloisHNScalarExtensionProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Every genuine recursive HN step commutes with finite Galois Hermitian
extension. The terminal step is included without a positive-rank assumption. -/
theorem hermitianHNStep_baseChange_hermitianScalarExtension_of_finiteGalois
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    (V.hermitianHNStep U).baseChange L =
      W.hermitianHNStep (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) (U.baseChange L) := by
  intro hLN hLS W hLH
  change W.toNormFamily.IsHermitian (hS := ⟨hLN⟩) at hLH
  by_cases hU : U = ⊤
  · subst U
    rw [V.hermitianHNStep_top, Submodule.baseChange_top]
    exact (W.hermitianHNStep_top (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH)).symm
  · have hUL : U.baseChange L ≠ ⊤ := by
      intro he
      apply hU
      apply (Submodule.baseChange_inj (A := L)).mp
      simpa only [Submodule.baseChange_top] using he
    let Q := V.quotientOfMeasurableBase U
    let QL := W.quotientOfMeasurableBase (U.baseChange L) (hS := ⟨hLS⟩)
    let hQL : QL.toNormFamily.IsHermitian (hS := ⟨hLN⟩) := hLH.quotient (U.baseChange L)
    let Qext := Q.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩) (hV := (hH.quotient U))
    let hQext := Q.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩) (hV := (hH.quotient U))
    let hr := finrank_quotient_pos_of_ne_top U hU
    let hrExt : 0 < Module.finrank L (L ⊗[K] (E ⧸ U)) :=
      (Module.finrank_baseChange (R := L) (S := K) (M' := E ⧸ U)).symm ▸ hr
    let hrL := finrank_quotient_pos_of_ne_top (U.baseChange L) hUL
    let e := tensorQuotientBaseChangeEquiv (L := L) U
    have he : ∀ x z, QL.toNormFamily.norm x
        (e.toLinearMap.baseChange x.abv.Completion z) = Qext.toNormFamily.norm x z := by
      intro x z
      exact V.toNormFamily.hermitianScalarExtension_quotient_norm_eq (hLN := ⟨hLN⟩) U x z
    have hD := Q.destabilizingSubspace_baseChange_hermitianScalarExtension_of_finiteGalois
      (L := L) (hH := (hH.quotient U)) hr
    change (Q.destabilizingSubspace (hV := (hH.quotient U)) hr).baseChange L =
      Qext.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hQext) hrExt at hD
    have hmap : ((Q.destabilizingSubspace (hV := (hH.quotient U)) hr).baseChange
        L).map e.toLinearMap = QL.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
            (hV := hQL) hrL :=
      (congrArg (fun D : Submodule L (L ⊗[K] (E ⧸ U)) ↦ D.map e.toLinearMap) hD).trans
        (Qext.map_destabilizingSubspace_eq_of_completed_isometry QL e (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
          (hV := hQext) (hW := hQL) hrExt hrL he)
    let T := V.hermitianHNStep U
    have hT : (T.baseChange L).map (U.baseChange L).mkQ =
        QL.destabilizingSubspace (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hQL) hrL := by
      calc
        _ = ((T.baseChange L).map (U.mkQ.baseChange L)).map e.toLinearMap := by
          rw [← Submodule.map_comp, tensorQuotientBaseChangeEquiv_comp_mkQ]
        _ = ((T.map U.mkQ).baseChange L).map e.toLinearMap := by
          rw [Submodule.map_baseChange]
        _ = ((Q.destabilizingSubspace (hV := (hH.quotient U)) hr).baseChange
            L).map e.toLinearMap := by
          rw [V.hermitianHNStep_map_mkQ U hU]
        _ = _ := hmap
    have hk : (U.baseChange L).mkQ.ker ≤ T.baseChange L := by
      rw [Submodule.ker_mkQ]
      exact Submodule.baseChange_mono L (V.le_hermitianHNStep U)
    change T.baseChange L = W.hermitianHNStep (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
        (hV := hLH) (U.baseChange L)
    conv_rhs => rw [hermitianHNStep, dite_eq_right hUL]
    exact (Submodule.comap_map_eq_self hk).symm.trans
      (congrArg (fun D : Submodule L ((L ⊗[K] E) ⧸ U.baseChange L) ↦
        D.comap (U.baseChange L).mkQ) hT)

/-- The entire actual recursive HN sequence commutes with finite Galois
Hermitian extension, including every repeated terminal term and rank zero. -/
theorem hermitianHNTerm_baseChange_hermitianScalarExtension_of_finiteGalois
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (n : ℕ) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    (V.hermitianHNTerm n).baseChange L =
      W.hermitianHNTerm (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) n := by
  intro hLN hLS W hLH
  change W.toNormFamily.IsHermitian (hS := ⟨hLN⟩) at hLH
  induction n with
  | zero => simp only [hermitianHNTerm_zero, Submodule.baseChange_bot]
  | succ n ih =>
    calc
      _ = (V.hermitianHNStep
          (V.hermitianHNTerm n)).baseChange L := rfl
      _ = W.hermitianHNStep (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH)
          ((V.hermitianHNTerm n).baseChange L) :=
        V.hermitianHNStep_baseChange_hermitianScalarExtension_of_finiteGalois
           _
      _ = W.hermitianHNStep (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) (W.hermitianHNTerm
          (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) n) :=
        congrArg (W.hermitianHNStep (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH)) ih
      _ = _ := rfl

/-- The first terminal index of the actual HN construction is preserved. -/
theorem hermitianHNLength_hermitianScalarExtension_of_finiteGalois
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    V.hermitianHNLength = W.hermitianHNLength (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) := by
  intro hLN hLS W hLH
  change W.toNormFamily.IsHermitian (hS := ⟨hLN⟩) at hLH
  have ht (n : ℕ) : V.hermitianHNTerm n = ⊤ ↔
      W.hermitianHNTerm (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) n = ⊤ := by
    have hi := (Submodule.baseChange_inj (A := L)
      (p := V.hermitianHNTerm n) (q := ⊤)).symm
    simpa only [Submodule.baseChange_top,
      V.hermitianHNTerm_baseChange_hermitianScalarExtension_of_finiteGalois
         n] using hi
  apply Nat.le_antisymm
  · by_contra h
    exact (V.hermitianHNTerm_ne_top_of_lt_length _
      (Nat.lt_of_not_ge h)) ((ht _).mpr (W.hermitianHNTerm_length_eq_top (hS := ⟨hLS⟩)
          (hN := ⟨hLN⟩) (hV := hLH)))
  · by_contra h
    exact (W.hermitianHNTerm_ne_top_of_lt_length (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH) _
      (Nat.lt_of_not_ge h)) ((ht _).mp (V.hermitianHNTerm_length_eq_top))

/-- The actual finite HN flags agree term by term under the produced length
identification. No target flag or stable-flag certificate is an input. -/
theorem hermitianHNFlag_baseChange_hermitianScalarExtension_of_finiteGalois
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    let hLH := V.hermitianScalarExtension_isHermitian (hL := ⟨hLN⟩)
    ∃ hlen : V.hermitianHNLength = W.hermitianHNLength (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) (hV := hLH),
      ∀ i : Fin (V.hermitianHNLength + 1),
        (V.hermitianHNFlag i).baseChange L =
          W.hermitianHNFlag (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
              (hV := hLH) (Fin.cast (congrArg (· + 1) hlen) i) := by
  intro hLN hLS W hLH
  refine ⟨V.hermitianHNLength_hermitianScalarExtension_of_finiteGalois,
    fun i ↦ ?_⟩
  exact V.hermitianHNTerm_baseChange_hermitianScalarExtension_of_finiteGalois i.val

/-- The genuine native actual quotient has the original maximal slope,
through its canonical completed tensor quotient isometry, in every rank. -/
theorem maximalSlope_quotient_hermitianScalarExtension_of_finiteGalois
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian] (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let W := V.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
    (W.quotientOfMeasurableBase (U.baseChange L) (hS := ⟨hLS⟩)).maximalSlope (hS := ⟨hLS⟩)
        (hN := ⟨hLN⟩) =
      (V.quotientOfMeasurableBase U).maximalSlope := by
  intro hLN hLS W
  let Q := V.quotientOfMeasurableBase U
  let Qext := Q.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩) (hV := (hH.quotient U))
  let QL := W.quotientOfMeasurableBase (U.baseChange L) (hS := ⟨hLS⟩)
  have he : Qext.maximalSlope (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) = QL.maximalSlope (hS := ⟨hLS⟩)
      (hN := ⟨hLN⟩) :=
    Qext.maximalSlope_eq_of_completed_isometry QL
    (tensorQuotientBaseChangeEquiv (L := L) U) (hS := ⟨hLS⟩) (hN := ⟨hLN⟩)
    (fun x z ↦ V.toNormFamily.hermitianScalarExtension_quotient_norm_eq (hLN := ⟨hLN⟩) U x z)
  exact he.symm.trans
    (Q.maximalSlope_hermitianScalarExtension_of_finiteGalois (hH := (hH.quotient U)))

/-- The actual scalar extension of every actual original HN factor is
semistable, by the produced finite-Galois semistability equivalence. -/
theorem isMeanSlopeSemistable_hermitianScalarExtension_hermitianHNFactor_of_finiteGalois
    (V : AdelicVectorBundle S E) [hcount : S.HasCommonCountableDenseSubfield]
    [hN : S.IsArchimedeanNormalized]
    [hH : V.toNormFamily.IsHermitian]
    (i : Fin (V.hermitianHNLength)) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (S := S) (L := L)
    let hLS := Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))
    let Q := V.hermitianHNFactor i
    (Q.hermitianScalarExtension (L := L) (hL := ⟨hLN⟩)
      (hV := (V.isHermitian_hermitianHNFactor i))).IsMeanSlopeSemistable
        (hS := ⟨hLS⟩) (hN := ⟨hLN⟩) := by
  intro hLN hLS Q
  exact (Q.isMeanSlopeSemistable_hermitianScalarExtension_iff_of_finiteGalois
    (L := L) (hH := (V.isHermitian_hermitianHNFactor i))).mpr
      (V.isMeanSlopeSemistable_hermitianHNFactor i)

end ScalarExtension

end ArakelovGeometry.AdelicVectorBundle

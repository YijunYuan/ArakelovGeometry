/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.HermitianClosedDestabilizerBaseChange
import ArakelovGeometry.AdelicVectorBundle.HermitianClosedSemistability
import ArakelovGeometry.AdelicVectorBundle.HermitianClosedScalarExtensionQuotient
import ArakelovGeometry.AdelicVectorBundle.HermitianGaloisHNScalarExtension

/-!
# The actual Hermitian HN flag over a closed algebraic extension

The actual first destabilizer of every genuine quotient transports through the
canonical completed quotient isometry. This preserves the canonical recursive
HN terms, first terminal length and native finite flag in every ambient rank.
-/

open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [PerfectField K] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {S : AdelicStructure K} [S.IsProper]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

local instance hermitianClosedHNScalarExtensionProper : (S.algebraicExtension L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

/-- Every genuine recursive HN step commutes with closed algebraic Hermitian
extension. The terminal step is included without a positive-rank assumption. -/
theorem hermitianHNStep_baseChange_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    let hLH := V.hermitianScalarExtension_isHermitian hcount hN hLN hH
    (V.hermitianHNStep (Or.inr hcount) hN hH U).baseChange L =
      W.hermitianHNStep hLS hLN hLH (U.baseChange L) := by
  intro hLN hLS W hLH
  change W.toNormFamily.IsHermitian hLN at hLH
  by_cases hU : U = ⊤
  · subst U
    rw [V.hermitianHNStep_top, Submodule.baseChange_top]
    exact (W.hermitianHNStep_top hLS hLN hLH).symm
  · have hUL : U.baseChange L ≠ ⊤ := by
      intro he
      apply hU
      apply (Submodule.baseChange_inj (A := L)).mp
      simpa only [Submodule.baseChange_top] using he
    let Q := V.quotientOfMeasurableBase U (Or.inr hcount)
    let QL := W.quotientOfMeasurableBase (U.baseChange L) hLS
    let hQL : QL.toNormFamily.IsHermitian hLN := hLH.quotient (U.baseChange L)
    let Qext := Q.hermitianScalarExtension (L := L) hcount hN hLN (hH.quotient U)
    let hQext := Q.hermitianScalarExtension_isHermitian hcount hN hLN (hH.quotient U)
    let hr := finrank_quotient_pos_of_ne_top U hU
    let hrExt : 0 < Module.finrank L (L ⊗[K] (E ⧸ U)) :=
      (Module.finrank_baseChange (R := L) (S := K) (M' := E ⧸ U)).symm ▸ hr
    let hrL := finrank_quotient_pos_of_ne_top (U.baseChange L) hUL
    let e := tensorQuotientBaseChangeEquiv (L := L) U
    have he : ∀ x z, QL.toNormFamily.norm x
        (e.toLinearMap.baseChange x.abv.Completion z) = Qext.toNormFamily.norm x z := by
      intro x z
      exact V.toNormFamily.hermitianScalarExtension_quotient_norm_eq hN hLN hH U x z
    have hD := Q.destabilizingSubspace_baseChange_hermitianScalarExtension_of_isAlgClosed
      (L := L) hcount hN (hH.quotient U) hr
    change (Q.destabilizingSubspace (Or.inr hcount) hN (hH.quotient U) hr).baseChange L =
      Qext.destabilizingSubspace hLS hLN hQext hrExt at hD
    have hmap : ((Q.destabilizingSubspace (Or.inr hcount) hN (hH.quotient U) hr).baseChange
        L).map e.toLinearMap = QL.destabilizingSubspace hLS hLN hQL hrL :=
      (congrArg (fun D : Submodule L (L ⊗[K] (E ⧸ U)) ↦ D.map e.toLinearMap) hD).trans
        (Qext.map_destabilizingSubspace_eq_of_completed_isometry QL e hLS hLN
          hQext hQL hrExt hrL he)
    let T := V.hermitianHNStep (Or.inr hcount) hN hH U
    have hT : (T.baseChange L).map (U.baseChange L).mkQ =
        QL.destabilizingSubspace hLS hLN hQL hrL := by
      calc
        _ = ((T.baseChange L).map (U.mkQ.baseChange L)).map e.toLinearMap := by
          rw [← Submodule.map_comp, tensorQuotientBaseChangeEquiv_comp_mkQ]
        _ = ((T.map U.mkQ).baseChange L).map e.toLinearMap := by
          rw [Submodule.map_baseChange]
        _ = ((Q.destabilizingSubspace (Or.inr hcount) hN (hH.quotient U) hr).baseChange
            L).map e.toLinearMap := by
          rw [V.hermitianHNStep_map_mkQ (Or.inr hcount) hN hH U hU]
        _ = _ := hmap
    have hk : (U.baseChange L).mkQ.ker ≤ T.baseChange L := by
      rw [Submodule.ker_mkQ]
      exact Submodule.baseChange_mono L (V.le_hermitianHNStep (Or.inr hcount) hN hH U)
    change T.baseChange L = W.hermitianHNStep hLS hLN hLH (U.baseChange L)
    conv_rhs => rw [hermitianHNStep, dif_neg hUL]
    exact (Submodule.comap_map_eq_self hk).symm.trans
      (congrArg (fun D : Submodule L ((L ⊗[K] E) ⧸ U.baseChange L) ↦
        D.comap (U.baseChange L).mkQ) hT)

/-- The entire actual recursive HN sequence commutes with closed algebraic
Hermitian extension, including every repeated terminal term and rank zero. -/
theorem hermitianHNTerm_baseChange_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (n : ℕ) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    let hLH := V.hermitianScalarExtension_isHermitian hcount hN hLN hH
    (V.hermitianHNTerm (Or.inr hcount) hN hH n).baseChange L =
      W.hermitianHNTerm hLS hLN hLH n := by
  intro hLN hLS W hLH
  change W.toNormFamily.IsHermitian hLN at hLH
  induction n with
  | zero => simp only [hermitianHNTerm_zero, Submodule.baseChange_bot]
  | succ n ih =>
    calc
      _ = (V.hermitianHNStep (Or.inr hcount) hN hH
          (V.hermitianHNTerm (Or.inr hcount) hN hH n)).baseChange L := rfl
      _ = W.hermitianHNStep hLS hLN hLH
          ((V.hermitianHNTerm (Or.inr hcount) hN hH n).baseChange L) :=
        V.hermitianHNStep_baseChange_hermitianScalarExtension_of_isAlgClosed
          hcount hN hH _
      _ = W.hermitianHNStep hLS hLN hLH (W.hermitianHNTerm hLS hLN hLH n) :=
        congrArg (W.hermitianHNStep hLS hLN hLH) ih
      _ = _ := rfl

/-- The first terminal index of the actual HN construction is preserved. -/
theorem hermitianHNLength_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    let hLH := V.hermitianScalarExtension_isHermitian hcount hN hLN hH
    V.hermitianHNLength (Or.inr hcount) hN hH = W.hermitianHNLength hLS hLN hLH := by
  intro hLN hLS W hLH
  change W.toNormFamily.IsHermitian hLN at hLH
  have ht (n : ℕ) : V.hermitianHNTerm (Or.inr hcount) hN hH n = ⊤ ↔
      W.hermitianHNTerm hLS hLN hLH n = ⊤ := by
    have hi := (Submodule.baseChange_inj (A := L)
      (p := V.hermitianHNTerm (Or.inr hcount) hN hH n) (q := ⊤)).symm
    simpa only [Submodule.baseChange_top,
      V.hermitianHNTerm_baseChange_hermitianScalarExtension_of_isAlgClosed
        hcount hN hH n] using hi
  apply Nat.le_antisymm
  · by_contra h
    exact (V.hermitianHNTerm_ne_top_of_lt_length (Or.inr hcount) hN hH _
      (Nat.lt_of_not_ge h)) ((ht _).mpr (W.hermitianHNTerm_length_eq_top hLS hLN hLH))
  · by_contra h
    exact (W.hermitianHNTerm_ne_top_of_lt_length hLS hLN hLH _
      (Nat.lt_of_not_ge h)) ((ht _).mp (V.hermitianHNTerm_length_eq_top (Or.inr hcount) hN hH))

/-- The actual finite HN flags agree term by term under the produced length
identification. No target flag or stable-flag certificate is an input. -/
theorem hermitianHNFlag_baseChange_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    let hLH := V.hermitianScalarExtension_isHermitian hcount hN hLN hH
    ∃ hlen : V.hermitianHNLength (Or.inr hcount) hN hH = W.hermitianHNLength hLS hLN hLH,
      ∀ i : Fin (V.hermitianHNLength (Or.inr hcount) hN hH + 1),
        (V.hermitianHNFlag (Or.inr hcount) hN hH i).baseChange L =
          W.hermitianHNFlag hLS hLN hLH (Fin.cast (congrArg (· + 1) hlen) i) := by
  intro hLN hLS W hLH
  refine ⟨V.hermitianHNLength_hermitianScalarExtension_of_isAlgClosed hcount hN hH,
    fun i ↦ ?_⟩
  exact V.hermitianHNTerm_baseChange_hermitianScalarExtension_of_isAlgClosed hcount hN hH i.val

/-- The genuine native actual quotient has the original maximal slope,
through its canonical completed tensor quotient isometry, in every rank. -/
theorem maximalSlope_quotient_hermitianScalarExtension_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN) (U : Submodule K E) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let W := V.hermitianScalarExtension (L := L) hcount hN hLN hH
    (W.quotientOfMeasurableBase (U.baseChange L) hLS).maximalSlope hLS hLN =
      (V.quotientOfMeasurableBase U (Or.inr hcount)).maximalSlope (Or.inr hcount) hN := by
  intro hLN hLS W
  let Q := V.quotientOfMeasurableBase U (Or.inr hcount)
  let Qext := Q.hermitianScalarExtension (L := L) hcount hN hLN (hH.quotient U)
  let QL := W.quotientOfMeasurableBase (U.baseChange L) hLS
  have he : Qext.maximalSlope hLS hLN = QL.maximalSlope hLS hLN :=
    Qext.maximalSlope_eq_of_completed_isometry QL
    (tensorQuotientBaseChangeEquiv (L := L) U) hLS hLN
    (fun x z ↦ V.toNormFamily.hermitianScalarExtension_quotient_norm_eq hN hLN hH U x z)
  exact he.symm.trans
    (Q.maximalSlope_hermitianScalarExtension_of_isAlgClosed hcount hN (hH.quotient U))

/-- The actual scalar extension of every actual original HN factor is
semistable, by the produced closed algebraic semistability equivalence. -/
theorem isMeanSlopeSemistable_hermitianScalarExtension_hermitianHNFactor_of_isAlgClosed
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : V.toNormFamily.IsHermitian hN)
    (i : Fin (V.hermitianHNLength (Or.inr hcount) hN hH)) :
    let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
    let hLS := Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L))
    let Q := V.hermitianHNFactor (Or.inr hcount) hN hH i
    (Q.hermitianScalarExtension (L := L) hcount hN hLN
      (V.isHermitian_hermitianHNFactor (Or.inr hcount) hN hH i)).IsMeanSlopeSemistable
        hLS hLN := by
  intro hLN hLS Q
  exact (Q.isMeanSlopeSemistable_hermitianScalarExtension_iff_of_isAlgClosed
    (L := L) hcount hN (V.isHermitian_hermitianHNFactor (Or.inr hcount) hN hH i)).mpr
      (V.isMeanSlopeSemistable_hermitianHNFactor (Or.inr hcount) hN hH i)

end ArakelovGeometry.AdelicVectorBundle

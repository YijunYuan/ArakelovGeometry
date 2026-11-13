/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Hermitian
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Expectation
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Quotient
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.CommonAdaptedBasis
public import ArakelovGeometry.LinearAlgebra.Filtration.Lift

/-!
# Chosen lifts of prescribed quotient filtrations

Adapted bases are produced separately on the actual adjacent quotients. Their
representatives form an ambient basis, with exactly the original quotient weights.
The resulting filtration need not be the ambient Harder--Narasimhan filtration.
-/

@[expose] public section

open Module

namespace Submodule

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {n : ℕ} (U : Fin (n + 1) → Submodule K E)
  (hU : Monotone U) (hzero : U 0 = ⊥) (htop : U (Fin.last n) = ⊤)

variable (F : ∀ i : Fin n, ℝ → Submodule K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
  (hF : ∀ i, Antitone (F i)) (hFbot : ∀ i, ∃ t, F i t = ⊥)
  (hFtop : ∀ i, ∃ t, F i t = ⊤)
  (hFleft : ∀ i t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F i s = F i t)

include hU hzero htop hF hFbot hFtop hFleft in
/-- Every family of actual adjacent-quotient filtrations admits a chosen lifting.
The bases and representatives are constructed, and the input weights are copied literally. -/
theorem exists_lift_prescribed_filtrations :
    ∃ (b : ∀ i : Fin n,
      Basis (Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)))
        K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
      (w : ∀ i : Fin n, Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)) → ℝ)
      (B : Basis
        (Σ i : Fin n, Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)))
        K E)
      (hB : ∀ i j, B ⟨i, j⟩ ∈ U i.succ) (R : ℝ → Submodule K E),
      (∀ i t, F i t = span K (b i '' {j | t ≤ w i j})) ∧
      (∀ i j, ((U i.castSucc).comap (U i.succ).subtype).mkQ
        ⟨B ⟨i, j⟩, hB i j⟩ = b i j) ∧
      (∀ k : Fin (n + 1), span K (B '' {a | a.1.val < k.val}) = U k) ∧
      (∀ t, R t = span K (B '' {a | t ≤ w a.1 a.2})) ∧
      Antitone R ∧ (∃ t, R t = ⊥) ∧ (∃ t, R t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → R s = R t) ∧
      ∀ i t, ((R t).comap (U i.succ).subtype).map
        ((U i.castSucc).comap (U i.succ).subtype).mkQ = F i t := by
  classical
  have hb : ∀ i : Fin n, ∃ (b :
      Basis (Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)))
        K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
      (w : Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)) → ℝ),
      ∀ t, F i t = span K (b '' {j | t ≤ w j}) := by
    intro i
    obtain ⟨b, w, _, hb, _⟩ := exists_common_weighted_basis
      (hF i) (hFbot i) (hFtop i) (hFleft i)
      (hF i) (hFbot i) (hFtop i) (hFleft i)
    exact ⟨b, w, hb⟩
  choose b w hb using hb
  obtain ⟨B, hB, hquot, hspan, hcuts⟩ :=
    exists_basis_lifting_weighted_quotients U hU hzero htop b w
  let R : ℝ → Submodule K E := fun t ↦ span K (B '' {a | t ≤ w a.1 a.2})
  refine ⟨b, w, B, hB, R, hb, hquot, hspan, fun _ ↦ rfl,
    antitone_span_weights B _, (span_weights_attains_bot_top B _).1,
    (span_weights_attains_bot_top B _).2, span_weights_locallyConstant_left B _, ?_⟩
  intro i t
  exact (hcuts i t).trans (hb i t).symm

end Submodule

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Restriction of the actual norm induces the inverse image of each literal ball. -/
theorem trivialFiltration_restrict (ξ : NormFamily (singleTrivialPlace K) E)
    [hξ : ξ.IsUltrametricAtFinitePlaces] (U : Submodule K E) (t : ℝ) :
    (ξ.restrict U).trivialFiltration (hξ := (hξ.restrict U)) t =
      (ξ.trivialFiltration t).comap U.subtype := by
  classical
  ext x
  change (ξ.restrict U).trivialSeminorm x ≤ Real.exp (-t) ↔
    ξ.trivialSeminorm (x : E) ≤ Real.exp (-t)
  simp only [trivialSeminorm_apply]
  rfl

/-- The actual subquotient norm of a filtration realization has the expected subquotient cuts. -/
theorem trivialFiltration_subquotient_ofTrivialFiltration [FiniteDimensional K E]
    (R : ℝ → Submodule K E) (hR : Antitone R)
    (hbot : ∃ t, R t = ⊥) (htop : ∃ t, R t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → R s = R t)
    (A B : Submodule K E) (t : ℝ) :
    (((ofTrivialFiltration R hR hbot htop hleft).restrict B).quotient
      (A.comap B.subtype)).trivialFiltration
        (hξ := (((ofTrivialFiltration_isUltrametricAtFinitePlaces R hR hbot htop hleft).restrict
          B).quotient
          (A.comap B.subtype))) t =
      ((R t).comap B.subtype).map (A.comap B.subtype).mkQ := by
  have he := trivialFiltration_pushforward
    ((ofTrivialFiltration R hR hbot htop hleft).restrict B)
    (hξ := ((ofTrivialFiltration_isUltrametricAtFinitePlaces R hR hbot htop hleft).restrict B))
    (A.comap B.subtype).mkQ (A.comap B.subtype).mkQ_surjective t
  rw [trivialFiltration_restrict _
    (hξ := (ofTrivialFiltration_isUltrametricAtFinitePlaces R hR hbot htop hleft)) B t,
    trivialFiltration_ofTrivialFiltration] at he
  exact he

/-- Equality of all literal cuts identifies the original actual norm family. -/
theorem eq_ofTrivialFiltration_of_cuts [FiniteDimensional K E]
    (ξ : NormFamily (singleTrivialPlace K) E) [hξ : ξ.IsUltrametricAtFinitePlaces]
    (F : ℝ → Submodule K E) (hF : Antitone F)
    (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hc : ∀ t, ξ.trivialFiltration t = F t) :
    ξ = ofTrivialFiltration F hF hbot htop hleft := by
  have he : ξ.trivialFiltration = F := funext hc
  simpa only [he] using (ofTrivialFiltration_trivialFiltration ξ).symm

/-- A lifted filtration realizes each prescribed subquotient norm, as an equality
of actual norm families on all completed vectors. -/
theorem subquotient_ofTrivialFiltration_eq [FiniteDimensional K E]
    (R : ℝ → Submodule K E) (hR : Antitone R)
    (hRbot : ∃ t, R t = ⊥) (hRtop : ∃ t, R t = ⊤)
    (hRleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → R s = R t)
    (A B : Submodule K E) (F : ℝ → Submodule K (B ⧸ A.comap B.subtype))
    (hF : Antitone F) (hFbot : ∃ t, F t = ⊥) (hFtop : ∃ t, F t = ⊤)
    (hFleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hc : ∀ t, ((R t).comap B.subtype).map (A.comap B.subtype).mkQ = F t) :
    ((ofTrivialFiltration R hR hRbot hRtop hRleft).restrict B).quotient
        (A.comap B.subtype) = ofTrivialFiltration F hF hFbot hFtop hFleft := by
  apply eq_ofTrivialFiltration_of_cuts _
    (hξ := (((ofTrivialFiltration_isUltrametricAtFinitePlaces R hR hRbot hRtop hRleft).restrict
      B).quotient
      (A.comap B.subtype))) F hF hFbot hFtop hFleft
  intro t
  exact (trivialFiltration_subquotient_ofTrivialFiltration
    R hR hRbot hRtop hRleft A B t).trans (hc t)

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

open AdelicStructure
open scoped BigOperators

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The actual arithmetic degree of a lifting is the sum of the actual degrees
of the prescribed quotient filtrations. Compatibility is the threshold equality
constructed by `Submodule.exists_lift_prescribed_filtrations`. -/
theorem degree_lift_eq_sum
    [hS : (singleTrivialPlace K).NormMeasurabilityHypotheses]
    [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
    {n : ℕ} (U : Fin (n + 1) → Submodule K E) (hU : Monotone U)
    (hzero : U 0 = ⊥) (htop : U (Fin.last n) = ⊤)
    (F : ∀ i : Fin n, ℝ → Submodule K
      ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
    (hF : ∀ i, Antitone (F i)) (hFbot : ∀ i, ∃ t, F i t = ⊥)
    (hFtop : ∀ i, ∃ t, F i t = ⊤)
    (hFleft : ∀ i t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F i s = F i t)
    (R : ℝ → Submodule K E) (hR : Antitone R)
    (hRbot : ∃ t, R t = ⊥) (hRtop : ∃ t, R t = ⊤)
    (hRleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → R s = R t)
    (hc : ∀ i t, ((R t).comap (U i.succ).subtype).map
      ((U i.castSucc).comap (U i.succ).subtype).mkQ = F i t) :
    (ofTrivialFiltration R hR hRbot hRtop hRleft).degree =
      ∑ i, (ofTrivialFiltration (F i) (hF i) (hFbot i) (hFtop i) (hFleft i)).degree := by
  let V := ofTrivialFiltration R hR hRbot hRtop hRleft
  have hV : V.toNormFamily.IsHermitian := by
    refine ⟨NormFamily.ofTrivialFiltration_isUltrametricAtFinitePlaces R hR hRbot hRtop hRleft, ?_⟩
    intro ω hω
    simp only [singleTrivialPlace_Ωinf, Set.mem_empty_iff_false] at hω
  have hq : ∀ i, V.flagQuotientOfNormMeasurability U i =
      ofTrivialFiltration (F i) (hF i) (hFbot i) (hFtop i) (hFleft i) := by
    intro i
    apply AdelicVectorBundle.ext
      (hξ := (V.flagQuotientOfNormMeasurability U i).toIsAdelic)
      (hη := (ofTrivialFiltration (F i) (hF i) (hFbot i) (hFtop i) (hFleft i)).toIsAdelic)
    exact NormFamily.subquotient_ofTrivialFiltration_eq R hR hRbot hRtop hRleft
      (U i.castSucc) (U i.succ) (F i) (hF i) (hFbot i) (hFtop i) (hFleft i) (hc i)
  exact (V.sum_flagQuotient_degree_eq_of_isHermitian U hU hzero htop (hV := hV)).symm.trans
    (Finset.sum_congr rfl (fun i _ ↦ congrArg (fun W ↦ W.degree) (hq i)))

/-- Adapted weights compute the actual degree of the realized filtration. -/
theorem degree_ofTrivialFiltration_eq_sum_weights
    [hS : (singleTrivialPlace K).NormMeasurabilityHypotheses]
    [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
    (F : ℝ → Submodule K E) (hF : Antitone F)
    (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    {ι : Type*} [Fintype ι] (b : Basis ι K E) (a : ι → ℝ)
    (hb : ∀ t, F t = Submodule.span K (b '' {i | t ≤ a i})) :
    (ofTrivialFiltration F hF hbot htop hleft).degree = ∑ i, a i := by
  rw [degree_eq_rank_mul_slope, slope_ofTrivialFiltration_eq_sum_weights
    F hF hbot htop hleft b a hb]
  by_cases hz : finrank K E = 0
  · have hc : Fintype.card ι = 0 := by rw [← finrank_eq_card_basis b, hz]
    let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz)

/-- Expectation is additive with rank multiplicities, including zero-rank quotients. -/
theorem finrank_mul_expectation_lift_eq_sum
    [hS : (singleTrivialPlace K).NormMeasurabilityHypotheses]
    [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
    {n : ℕ} (U : Fin (n + 1) → Submodule K E) (hU : Monotone U)
    (hzero : U 0 = ⊥) (htop : U (Fin.last n) = ⊤)
    (F : ∀ i : Fin n, ℝ → Submodule K
      ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
    (hF : ∀ i, Antitone (F i)) (hFbot : ∀ i, ∃ t, F i t = ⊥)
    (hFtop : ∀ i, ∃ t, F i t = ⊤)
    (hFleft : ∀ i t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F i s = F i t)
    (R : ℝ → Submodule K E) (hR : Antitone R)
    (hRbot : ∃ t, R t = ⊥) (hRtop : ∃ t, R t = ⊤)
    (hRleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → R s = R t)
    (hc : ∀ i t, ((R t).comap (U i.succ).subtype).map
      ((U i.castSucc).comap (U i.succ).subtype).mkQ = F i t) :
    (finrank K E : ℝ) * Submodule.filtrationExpectation R =
      ∑ i, (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype) : ℝ) *
        Submodule.filtrationExpectation (F i) := by
  have he := degree_lift_eq_sum U hU hzero htop F hF hFbot hFtop hFleft
    R hR hRbot hRtop hRleft hc
  simpa only [degree_eq_rank_mul_slope, slope_ofTrivialFiltration_eq_expectation] using he

/-- Pairing with the original flag groups the unchanged quotient weights by block. -/
theorem pairing_lift_eq_sum_quotient_degrees
    [hS : (singleTrivialPlace K).NormMeasurabilityHypotheses]
    [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
    {n : ℕ} (U : Fin (n + 1) → Submodule K E)
    {ι : Fin n → Type*}
    (b : ∀ i, Basis (ι i) K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
    (w : ∀ i, ι i → ℝ) (B : Basis (Σ i, ι i) K E)
    (hspan : ∀ k : Fin (n + 1), Submodule.span K (B '' {a | a.1.val < k.val}) = U k)
    (F : ∀ i : Fin n, ℝ → Submodule K
      ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
    (hF : ∀ i, Antitone (F i)) (hFbot : ∀ i, ∃ t, F i t = ⊥)
    (hFtop : ∀ i, ∃ t, F i t = ⊤)
    (hFleft : ∀ i t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F i s = F i t)
    (hb : ∀ i t, F i t = Submodule.span K (b i '' {j | t ≤ w i j}))
    (R : ℝ → Submodule K E)
    (hR : ∀ t, R t = Submodule.span K (B '' {j | t ≤ w j.1 j.2}))
    (a : Fin n → ℝ) (ha : Antitone a) :
    (finrank K E : ℝ) * Submodule.filtrationPairing
      (fun t ↦ ⨆ (i : Fin n) (_ : t ≤ a i), U i.succ) R =
        ∑ i, a i * (ofTrivialFiltration (F i) (hF i) (hFbot i)
          (hFtop i) (hFleft i)).degree := by
  classical
  let : ∀ i, Fintype (ι i) := fun i ↦ FiniteDimensional.fintypeBasisIndex (b i)
  simp_rw [degree_ofTrivialFiltration_eq_sum_weights _ _ _ _ _ (b _) (w _) (hb _)]
  rw [Submodule.filtrationPairing_eq_sum_weights B (fun j ↦ a j.1)
    (fun j ↦ w j.1 j.2) (Submodule.iSup_flag_eq_span_weights U B hspan a ha) hR]
  have hs : (∑ j : Σ i, ι i, a j.1 * w j.1 j.2) = ∑ i, a i * ∑ j, w i j := by
    simp only [Fintype.sum_sigma, Finset.mul_sum]
  by_cases hz : finrank K E = 0
  · have hc : Fintype.card (Σ i, ι i) = 0 := by
      rw [← finrank_eq_card_basis B, hz]
    let : IsEmpty (Σ i, ι i) := Fintype.card_eq_zero_iff.mp hc
    rw [← hs]
    simp
  · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz), hs]

end ArakelovGeometry.AdelicVectorBundle

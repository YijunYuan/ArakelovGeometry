/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Lift
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.PositiveDegree
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Degree

/-!
# Chosen lifts of the actual quotient HN filtrations

The input is the actual Hermitian HN filtration of every adjacent quotient.
Its intrinsic weighted graded sum is the actual arithmetic degree. The chosen
ambient lifting retains these inputs and has the expected slope and pairing.
-/

@[expose] public section

open Module
open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {S : AdelicStructure K} [S.IsProper]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hV : V.toNormFamily.IsHermitian hN)

/-- The actual HN filtration has the original bundle's degree as its intrinsic
weighted graded sum. This statement includes rank zero. -/
theorem finsum_hermitianHNFiltration_eq_degree :
    (∑ᶠ t : ℝ, t * (finrank K
      (Submodule.FiltrationGraded (V.hermitianHNFiltration hS hN hV) t) : ℝ)) =
        V.degree hS hN := by
  classical
  let a : Fin (V.hermitianHNLength hS hN hV) → ℝ :=
    fun i ↦ (V.hermitianHNFactor hS hN hV i).slope hS hN
  have hz (t : ℝ) (ht : t ∉ Set.range a) :
      finrank K (Submodule.FiltrationGraded (V.hermitianHNFiltration hS hN hV) t) = 0 := by
    have hp : Submodule.filtrationRightLimit (V.hermitianHNFiltration hS hN hV) t =
        V.hermitianHNFiltration hS hN hV t :=
      V.hermitianHNFiltrationPlus_eq_of_ne_factor_slope hS hN hV t
        (fun i hi ↦ ht ⟨i, hi⟩)
    simp only [Submodule.FiltrationGraded, hp, Submodule.comap_subtype_self,
      Submodule.finrank_quotient, finrank_top, Nat.sub_self]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image a) (by
    intro t ht
    by_contra hn
    exact ht (by rw [hz t (by simpa using hn), Nat.cast_zero, mul_zero]))]
  rw [Finset.sum_image (fun i _ j _ h ↦
    (V.hermitianHNFactor_slope_strictAnti hS hN hV).injective h)]
  have he (i : Fin (V.hermitianHNLength hS hN hV)) :
      finrank K (Submodule.FiltrationGraded (V.hermitianHNFiltration hS hN hV) (a i)) =
        finrank K ((V.hermitianHNTerm hS hN hV (i.val + 1)).map
          (V.hermitianHNTerm hS hN hV i.val).mkQ) := by
    have hp : Submodule.filtrationRightLimit (V.hermitianHNFiltration hS hN hV) (a i) =
        V.hermitianHNFlag hS hN hV i.castSucc :=
      V.hermitianHNFiltrationPlus_factor_slope hS hN hV i
    have hf : V.hermitianHNFiltration hS hN hV (a i) =
        V.hermitianHNFlag hS hN hV i.succ :=
      V.hermitianHNFiltration_factor_slope hS hN hV i
    simp only [Submodule.FiltrationGraded, hp, hf]
    exact V.finrank_hermitianHNFlagQuotient_eq hS hN hV i
  simp_rw [he]
  simpa only [a, mul_comm] using V.sum_hermitianHNFactor_rank_mul_slope_eq_degree hS hN hV

/-- The expectation of the actual Hermitian HN filtration equals the actual mean slope. -/
theorem expectation_hermitianHNFiltration_eq_slope :
    Submodule.filtrationExpectation (V.hermitianHNFiltration hS hN hV) = V.slope hS hN := by
  rw [Submodule.filtrationExpectation, V.finsum_hermitianHNFiltration_eq_degree, slope]

/-- Lift the actual HN filtrations on all adjacent quotients. The witnesses retain
all quotient bases, their unchanged weights, every induced cut, and both paper identities. -/
theorem exists_hermitianHN_quotient_lift
    {n : ℕ} (U : Fin (n + 1) → Submodule K E) (hU : Monotone U)
    (hzero : U 0 = ⊥) (htop : U (Fin.last n) = ⊤) :
    let F := fun i : Fin n ↦ (V.flagQuotientOfMeasurableBase U hS i).hermitianHNFiltration
      hS hN ((hV.restrict (U i.succ)).quotient ((U i.castSucc).comap (U i.succ).subtype))
    ∃ (b : ∀ i : Fin n,
      Basis (Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)))
        K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
      (w : ∀ i : Fin n, Fin (finrank K
        ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)) → ℝ)
      (B : Basis
        (Σ i : Fin n, Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)))
        K E)
      (hB : ∀ i j, B ⟨i, j⟩ ∈ U i.succ) (R : ℝ → Submodule K E),
      (∀ i t, F i t = Submodule.span K (b i '' {j | t ≤ w i j})) ∧
      (∀ i j, ((U i.castSucc).comap (U i.succ).subtype).mkQ
        ⟨B ⟨i, j⟩, hB i j⟩ = b i j) ∧
      (∀ k : Fin (n + 1), Submodule.span K (B '' {a | a.1.val < k.val}) = U k) ∧
      (∀ t, R t = Submodule.span K (B '' {a | t ≤ w a.1 a.2})) ∧
      Antitone R ∧ (∃ t, R t = ⊥) ∧ (∃ t, R t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → R s = R t) ∧
      (∀ i t, ((R t).comap (U i.succ).subtype).map
        ((U i.castSucc).comap (U i.succ).subtype).mkQ = F i t) ∧
      Submodule.filtrationExpectation R = V.slope hS hN ∧
      ∀ a : Fin n → ℝ, Antitone a →
        (finrank K E : ℝ) * Submodule.filtrationPairing
          (fun t ↦ ⨆ (i : Fin n) (_ : t ≤ a i), U i.succ) R =
            ∑ i, a i * (V.flagQuotientOfMeasurableBase U hS i).degree hS hN := by
  classical
  let Q := V.flagQuotientOfMeasurableBase U hS
  let hQ := fun i : Fin n ↦
    (hV.restrict (U i.succ)).quotient ((U i.castSucc).comap (U i.succ).subtype)
  let F := fun i : Fin n ↦ (Q i).hermitianHNFiltration hS hN (hQ i)
  have hF : ∀ i, Antitone (F i) := fun i ↦ (Q i).hermitianHNFiltration_antitone hS hN (hQ i)
  have hFbot : ∀ i, ∃ t, F i t = ⊥ := by
    intro i
    obtain ⟨t, ht⟩ := (Q i).hermitianHNFiltration_separated hS hN (hQ i)
    exact ⟨t + 1, ht _ (by linarith)⟩
  have hFtop : ∀ i, ∃ t, F i t = ⊤ := by
    intro i
    obtain ⟨t, ht⟩ := (Q i).hermitianHNFiltration_exhaustive hS hN (hQ i)
    exact ⟨t, ht _ le_rfl⟩
  have hFleft : ∀ i t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F i s = F i t := by
    intro i t
    obtain ⟨ε, hε, he⟩ := (Q i).hermitianHNFiltration_locallyConstantLeft hS hN (hQ i) t
    refine ⟨ε, hε, fun s hs hst ↦ ?_⟩
    have hr := he (t - s) (by linarith) (by linarith)
    simpa only [sub_sub_cancel] using hr
  obtain ⟨b, w, B, hB, R, hb, hquot, hspan, hRspan, hR, hRbot, hRtop, hRleft, hc⟩ :=
    Submodule.exists_lift_prescribed_filtrations U hU hzero htop F hF hFbot hFtop hFleft
  refine ⟨b, w, B, hB, R, hb, hquot, hspan, hRspan, hR, hRbot, hRtop, hRleft, hc, ?_, ?_⟩
  · have he : (finrank K E : ℝ) * Submodule.filtrationExpectation R = V.degree hS hN := by
      rw [Submodule.filtrationExpectation_eq_sum_weights B _ hRspan]
      have hw (i : Fin n) : (∑ j, w i j) = (Q i).degree hS hN := by
        rw [← Submodule.finsum_weight_mul_finrank_filtrationGraded (b i) (w i) (hb i)]
        exact (Q i).finsum_hermitianHNFiltration_eq_degree hS hN (hQ i)
      have hs : (∑ j, w j.1 j.2) = V.degree hS hN := by
        rw [Fintype.sum_sigma]
        simp_rw [hw]
        exact V.sum_flagQuotient_degree_eq_of_isHermitian U hU hzero htop hS hN hV
      by_cases hz : finrank K E = 0
      · rw [V.degree_eq_zero_of_finrank_eq_zero hS hN hz, hz, Nat.cast_zero, zero_mul]
      · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz), hs]
    by_cases hz : finrank K E = 0
    · simp only [Submodule.filtrationExpectation, slope, hz, Nat.cast_zero, div_zero]
    · rw [slope]
      exact (eq_div_iff (Nat.cast_ne_zero.mpr hz)).mpr (by simpa [mul_comm] using he)
  · intro a ha
    rw [Submodule.filtrationPairing_eq_sum_weights B (fun j ↦ a j.1)
      (fun j ↦ w j.1 j.2) (Submodule.iSup_flag_eq_span_weights U B hspan a ha) hRspan]
    have hw (i : Fin n) : (∑ j, w i j) = (Q i).degree hS hN := by
      rw [← Submodule.finsum_weight_mul_finrank_filtrationGraded (b i) (w i) (hb i)]
      exact (Q i).finsum_hermitianHNFiltration_eq_degree hS hN (hQ i)
    have hs : (∑ j, a j.1 * w j.1 j.2) = ∑ i, a i * (Q i).degree hS hN := by
      simp only [Fintype.sum_sigma, ← Finset.mul_sum, hw]
    by_cases hz : finrank K E = 0
    · have hc : Fintype.card (Σ i : Fin n,
          Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))) = 0 := by
        rw [← finrank_eq_card_basis B, hz]
      letI : IsEmpty (Σ i : Fin n,
        Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))) :=
          Fintype.card_eq_zero_iff.mp hc
      rw [← hs]
      simp
    · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz), hs]

end ArakelovGeometry.AdelicVectorBundle

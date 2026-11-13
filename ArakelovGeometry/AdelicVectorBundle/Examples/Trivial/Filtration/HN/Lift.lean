/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Lift
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Degree
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.PositiveDegree

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
  (V : AdelicVectorBundle S)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian]

omit [FiniteDimensional K E] in
private theorem finrank_grade_of_endpoints (F : ℝ → Submodule K E) (t : ℝ)
    (A B : Submodule K E) (hA : F t = A) (hB : Submodule.filtrationRightLimit F t = B) :
    finrank K (Submodule.FiltrationGraded F t) = finrank K (A ⧸ B.comap A.subtype) := by
  unfold Submodule.FiltrationGraded
  rw [hA, hB]

private theorem finrank_self_quotient (A : Submodule K E) :
    finrank K (A ⧸ A.comap A.subtype) = 0 := by
  rw [Submodule.comap_subtype_self, Submodule.finrank_quotient,
    finrank_top, Nat.sub_self]

/-- The actual HN filtration has the original bundle's degree as its intrinsic
weighted graded sum. This statement includes rank zero. -/
theorem finsum_hermitianHNFiltration_eq_degree :
    (∑ᶠ t : ℝ, t * (finrank K
      (Submodule.FiltrationGraded (V.hermitianHNFiltration) t) : ℝ)) =
        V.degree := by
  classical
  let a : Fin (V.hermitianHNLength) → ℝ :=
    fun i ↦ (V.hermitianHNFactor i).slope
  have hz (t : ℝ) (ht : t ∉ Set.range a) :
      finrank K (Submodule.FiltrationGraded (V.hermitianHNFiltration) t) = 0 := by
    have hp : Submodule.filtrationRightLimit (V.hermitianHNFiltration) t =
        V.hermitianHNFiltration t :=
      V.hermitianHNFiltrationPlus_eq_of_ne_factor_slope t
        (fun i hi ↦ ht ⟨i, hi⟩)
    exact (finrank_grade_of_endpoints _ t _ _ rfl hp).trans (finrank_self_quotient _)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image a) (by
    intro t ht
    by_contra hn
    apply ht
    simpa only [Nat.cast_zero, mul_zero] using
      (congrArg (fun r : ℕ ↦ t * (r : ℝ)) (hz t (by simpa using hn))))]
  rw [Finset.sum_image (fun i _ j _ h ↦
    (V.hermitianHNFactor_slope_strictAnti).injective h)]
  have he (i : Fin (V.hermitianHNLength)) :
      finrank K (Submodule.FiltrationGraded (V.hermitianHNFiltration) (a i)) =
        finrank K ((V.hermitianHNTerm (i.val + 1)).map
          (V.hermitianHNTerm i.val).mkQ) := by
    have hp : Submodule.filtrationRightLimit (V.hermitianHNFiltration) (a i) =
        V.hermitianHNFlag i.castSucc :=
      V.hermitianHNFiltrationPlus_factor_slope i
    have hf : V.hermitianHNFiltration (a i) =
        V.hermitianHNFlag i.succ :=
      V.hermitianHNFiltration_factor_slope i
    exact (finrank_grade_of_endpoints _ (a i) _ _ hf hp).trans
      (V.finrank_hermitianHNFlagQuotient_eq i)
  calc
    _ = ∑ i, a i * (finrank K ((V.hermitianHNTerm (i.val + 1)).map
        (V.hermitianHNTerm i.val).mkQ) : ℝ) :=
      Finset.sum_congr rfl (fun i _ ↦ congrArg (fun r : ℕ ↦ a i * (r : ℝ)) (he i))
    _ = V.degree := by
      simpa only [a, mul_comm] using
        V.sum_hermitianHNFactor_rank_mul_slope_eq_degree

/-- The expectation of the actual Hermitian HN filtration equals the actual mean slope. -/
theorem expectation_hermitianHNFiltration_eq_slope :
    Submodule.filtrationExpectation (V.hermitianHNFiltration) = V.slope := by
  rw [Submodule.filtrationExpectation, V.finsum_hermitianHNFiltration_eq_degree, slope]

/-- Lift the actual HN filtrations on all adjacent quotients. The witnesses retain
all quotient bases, their unchanged weights, every induced cut, and both paper identities. -/
theorem exists_hermitianHN_quotient_lift
    {n : ℕ} (U : Fin (n + 1) → Submodule K V) (hU : Monotone U)
    (hzero : U 0 = ⊥) (htop : U (Fin.last n) = ⊤) :
    let F := fun i : Fin n ↦ (V.flagQuotientOfMeasurableBase U i).hermitianHNFiltration
      (hV := ((hV.restrict (U i.succ)).quotient ((U i.castSucc).comap (U i.succ).subtype)))
    ∃ (b : ∀ i : Fin n,
      Basis (Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)))
        K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))
      (w : ∀ i : Fin n, Fin (finrank K
        ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)) → ℝ)
      (B : Basis
        (Σ i : Fin n, Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)))
        K V)
      (hB : ∀ i j, B ⟨i, j⟩ ∈ U i.succ) (R : ℝ → Submodule K V),
      (∀ i t, F i t = Submodule.span K (b i '' {j | t ≤ w i j})) ∧
      (∀ i j, ((U i.castSucc).comap (U i.succ).subtype).mkQ
        ⟨B ⟨i, j⟩, hB i j⟩ = b i j) ∧
      (∀ k : Fin (n + 1), Submodule.span K (B '' {a | a.1.val < k.val}) = U k) ∧
      (∀ t, R t = Submodule.span K (B '' {a | t ≤ w a.1 a.2})) ∧
      Antitone R ∧ (∃ t, R t = ⊥) ∧ (∃ t, R t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → R s = R t) ∧
      (∀ i t, ((R t).comap (U i.succ).subtype).map
        ((U i.castSucc).comap (U i.succ).subtype).mkQ = F i t) ∧
      Submodule.filtrationExpectation R = V.slope ∧
      ∀ a : Fin n → ℝ, Antitone a →
        (finrank K V : ℝ) * Submodule.filtrationPairing
          (fun t ↦ ⨆ (i : Fin n) (_ : t ≤ a i), U i.succ) R =
            ∑ i, a i * (V.flagQuotientOfMeasurableBase U i).degree := by
  classical
  let Q := V.flagQuotientOfMeasurableBase U
  let hQ := fun i : Fin n ↦
    (hV.restrict (U i.succ)).quotient ((U i.castSucc).comap (U i.succ).subtype)
  let F := fun i : Fin n ↦ (Q i).hermitianHNFiltration (hV := (hQ i))
  have hF : ∀ i, Antitone (F i) := fun i ↦ (Q i).hermitianHNFiltration_antitone (hV := (hQ i))
  have hFbot : ∀ i, ∃ t, F i t = ⊥ := by
    intro i
    obtain ⟨t, ht⟩ := (Q i).hermitianHNFiltration_separated (hV := (hQ i))
    exact ⟨t + 1, ht _ (by linarith)⟩
  have hFtop : ∀ i, ∃ t, F i t = ⊤ := by
    intro i
    obtain ⟨t, ht⟩ := (Q i).hermitianHNFiltration_exhaustive (hV := (hQ i))
    exact ⟨t, ht _ le_rfl⟩
  have hFleft : ∀ i t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F i s = F i t := by
    intro i t
    obtain ⟨ε, hε, he⟩ := (Q i).hermitianHNFiltration_locallyConstantLeft (hV := (hQ i)) t
    refine ⟨ε, hε, fun s hs hst ↦ ?_⟩
    have hr := he (t - s) (by linarith) (by linarith)
    simpa only [sub_sub_cancel] using hr
  obtain ⟨b, w, B, hB, R, hb, hquot, hspan, hRspan, hR, hRbot, hRtop, hRleft, hc⟩ :=
    Submodule.exists_lift_prescribed_filtrations U hU hzero htop F hF hFbot hFtop hFleft
  refine ⟨b, w, B, hB, R, hb, hquot, hspan, hRspan, hR, hRbot, hRtop, hRleft, hc, ?_, ?_⟩
  · have he : (finrank K V : ℝ) * Submodule.filtrationExpectation R = V.degree := by
      rw [Submodule.filtrationExpectation_eq_sum_weights B _ hRspan]
      have hw (i : Fin n) : (∑ j, w i j) = (Q i).degree := by
        rw [← Submodule.finsum_weight_mul_finrank_filtrationGraded (b i) (w i) (hb i)]
        exact (Q i).finsum_hermitianHNFiltration_eq_degree (hV := (hQ i))
      have hs : (∑ j : Σ i : Fin n,
          Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)),
          w j.1 j.2) = V.degree := by
        rw [Fintype.sum_sigma]
        simp_rw [hw]
        exact V.sum_flagQuotient_degree_eq_of_isHermitian U hU hzero htop
      by_cases hz : finrank K V = 0
      · rw [V.degree_eq_zero_of_finrank_eq_zero hz, hz, Nat.cast_zero, zero_mul]
      · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz), hs]
    by_cases hz : finrank K V = 0
    · simp only [Submodule.filtrationExpectation, slope, hz, Nat.cast_zero, div_zero]
    · rw [slope]
      exact (eq_div_iff (Nat.cast_ne_zero.mpr hz)).mpr (by simpa [mul_comm] using he)
  · intro a ha
    rw [Submodule.filtrationPairing_eq_sum_weights B (fun j ↦ a j.1)
      (fun j ↦ w j.1 j.2) (Submodule.iSup_flag_eq_span_weights U B hspan a ha) hRspan]
    have hw (i : Fin n) : (∑ j, w i j) = (Q i).degree := by
      rw [← Submodule.finsum_weight_mul_finrank_filtrationGraded (b i) (w i) (hb i)]
      exact (Q i).finsum_hermitianHNFiltration_eq_degree (hV := (hQ i))
    have hs : (∑ j : Σ i : Fin n,
        Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype)),
        a j.1 * w j.1 j.2) = ∑ i, a i * (Q i).degree := by
      simp only [Fintype.sum_sigma, ← Finset.mul_sum, hw]
    by_cases hz : finrank K V = 0
    · have hc : Fintype.card (Σ i : Fin n,
          Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))) = 0 := by
        rw [← finrank_eq_card_basis B, hz]
      let : IsEmpty (Σ i : Fin n,
        Fin (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype))) :=
          Fintype.card_eq_zero_iff.mp hc
      rw [← hs]
      simp
    · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hz), hs]

end ArakelovGeometry.AdelicVectorBundle

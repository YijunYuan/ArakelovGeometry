/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Expectation
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Quotient

/-!
# The graded-degree interpretation of intrinsic pairing

Each grade of `F` carries the restriction and quotient of the norm associated
to the OTHER filtration `G`. The actual quotient-ball theorem identifies its
filtration, and the actual degree theorem computes its degree.
-/

@[expose] public section

open Module

namespace Submodule

variable {K E ι : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype ι]

/-- The degree weight of a fixed first grade is the sum of the second weights in that fiber. -/
theorem finsum_snd_mul_filtrationJointMultiplicity (b : Basis ι K E) (a c : ι → ℝ)
    {F G : ℝ → Submodule K E}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ a i}))
    (hG : ∀ t, G t = span K (b '' {i | t ≤ c i})) (s : ℝ) :
    (∑ᶠ t : ℝ, t * (filtrationJointMultiplicity F G s t : ℝ)) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ a i = s), c i := by
  classical
  let J := Finset.univ.filter (fun i ↦ a i = s)
  have hm (t : ℝ) : filtrationJointMultiplicity F G s t =
      (J.filter (fun i ↦ c i = t)).card := by
    rw [filtrationJointMultiplicity_eq_card b a c hF hG]
    simp only [J, Finset.filter_filter]
  rw [finsum_eq_sum_of_support_subset _ (s := J.image c) (by
    intro t ht
    by_contra hn
    have hz : J.filter (fun i ↦ c i = t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hn (Finset.mem_image.mpr
        ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩)
    exact ht (by simp only [hm, hz, Finset.card_empty, Nat.cast_zero, mul_zero]))]
  simp_rw [hm]
  have he := Finset.sum_fiberwise_of_maps_to'
    (s := J) (t := J.image c) (g := c)
    (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩) (fun t : ℝ ↦ t)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using he

end Submodule

namespace ArakelovGeometry.AdelicVectorBundle

open AdelicStructure Submodule

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The actual `F`-grade, carrying the norm induced from the specified bundle `V`. -/
noncomputable abbrev filtrationGradedBundle (V : AdelicVectorBundle (singleTrivialPlace K))
    (F : ℝ → Submodule K V) (s : ℝ)
    [hS : (singleTrivialPlace K).NormMeasurabilityHypotheses] :
    AdelicVectorBundle (singleTrivialPlace K) :=
  (V.restrictOfNormMeasurability (F s)).quotientOfNormMeasurability
    ((filtrationRightLimit F s).comap (F s).subtype)

variable (V : AdelicVectorBundle (singleTrivialPlace K))
  [hS : (singleTrivialPlace K).NormMeasurabilityHypotheses]
  [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsUltrametricAtFinitePlaces]
  (F : ℝ → Submodule K V)

omit hN in
/-- Literal balls on the actual subquotient are the induced cuts on the shared grade carrier. -/
theorem trivialFiltration_filtrationGradedBundle (s t : ℝ) :
    (V.filtrationGradedBundle F s).toNormFamily.trivialFiltration
      (hξ := ((hV.restrict (F s)).quotient ((filtrationRightLimit F s).comap (F s).subtype))) t =
      filtrationOnGraded F (V.toNormFamily.trivialFiltration) s t := by
  have he := NormFamily.trivialFiltration_pushforward (V.toNormFamily.restrict (F s))
    (hξ := (hV.restrict (F s))) ((filtrationRightLimit F s).comap (F s).subtype).mkQ
    ((filtrationRightLimit F s).comap (F s).subtype).mkQ_surjective t
  have hr : (V.toNormFamily.restrict (F s)).trivialFiltration (hξ := (hV.restrict (F s))) t =
      (V.toNormFamily.trivialFiltration t).comap (F s).subtype := by
    classical
    ext x
    change (V.toNormFamily.restrict (F s)).trivialSeminorm x ≤ Real.exp (-t) ↔
      V.toNormFamily.trivialSeminorm (x : V) ≤ Real.exp (-t)
    simp only [NormFamily.trivialSeminorm_apply]
    rfl
  rw [hr] at he
  exact he

/-- The actual induced degree equals the second-weight sum of intrinsic joint grades. -/
theorem degree_filtrationGradedBundle_eq_jointMultiplicity (hF : Antitone F) (s : ℝ) :
    (V.filtrationGradedBundle F s).degree =
      ∑ᶠ t : ℝ, t *
        (filtrationJointMultiplicity F (V.toNormFamily.trivialFiltration) s t : ℝ) := by
  have hc := funext (V.trivialFiltration_filtrationGradedBundle F s)
  rw [degree_eq_finsum_trivialFiltration _
    (hV := ((hV.restrict (F s)).quotient ((filtrationRightLimit F s).comap (F s).subtype))), hc]
  simp only [finrank_filtrationGraded_filtrationOnGraded hF
    (V.toNormFamily.antitone_trivialFiltration)]

/-- Compute each actual graded degree in any common adapted basis. -/
theorem degree_filtrationGradedBundle_eq_sum_weights (hF : Antitone F)
    {ι : Type*} [Fintype ι] (b : Basis ι K V) (a c : ι → ℝ)
    (hFa : ∀ t, F t = span K (b '' {i | t ≤ a i}))
    (hGc : ∀ t, V.toNormFamily.trivialFiltration t = span K (b '' {i | t ≤ c i}))
    (s : ℝ) :
    (V.filtrationGradedBundle F s).degree =
      ∑ i ∈ Finset.univ.filter (fun i ↦ a i = s), c i := by
  rw [V.degree_filtrationGradedBundle_eq_jointMultiplicity F hF,
    finsum_snd_mul_filtrationJointMultiplicity b a c hFa hGc]

/-- The graded degree sum equals the intrinsic pairing; each grade uses the norm from `V`. -/
theorem filtrationPairing_eq_finsum_graded_degree_of_common_basis (hF : Antitone F)
    {ι : Type*} [Finite ι] (b : Basis ι K V) (a c : ι → ℝ)
    (hFa : ∀ t, F t = span K (b '' {i | t ≤ a i}))
    (hGc : ∀ t, V.toNormFamily.trivialFiltration t = span K (b '' {i | t ≤ c i})) :
    filtrationPairing F (V.toNormFamily.trivialFiltration) =
      (∑ᶠ s : ℝ, s * (V.filtrationGradedBundle F s).degree) / finrank K V := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [filtrationPairing_eq_sum_weights b a c hFa hGc]
  congr 1
  simp_rw [V.degree_filtrationGradedBundle_eq_sum_weights F hF b a c hFa hGc]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image a) (by
    intro s hs
    by_contra hn
    have hz : Finset.univ.filter (fun i ↦ a i = s) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
    exact hs (by simp only [hz, Finset.sum_empty, mul_zero]))]
  have he := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset ι)) (t := Finset.univ.image a) (g := a)
    (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩) (fun i ↦ a i * c i)
  rw [← he]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

omit V hV in
/-- CM Proposition 5.4.1 with normalized pairing and the OTHER filtration's actual norm. -/
theorem filtrationPairing_eq_finsum_graded_degree (F : ℝ → Submodule K E)
    (hF : Antitone F) (hFbot : ∃ t, F t = ⊥) (hFtop : ∃ t, F t = ⊤)
    (hFleft : ∀ t, ∃ ε > 0, ∀ u, t - ε < u → u ≤ t → F u = F t)
    (G : ℝ → Submodule K E)
    (hG : Antitone G) (hGbot : ∃ t, G t = ⊥) (hGtop : ∃ t, G t = ⊤)
    (hGleft : ∀ t, ∃ ε > 0, ∀ u, t - ε < u → u ≤ t → G u = G t) :
    filtrationPairing F G =
      (∑ᶠ s : ℝ, s * ((ofTrivialFiltration G hG hGbot hGtop hGleft).filtrationGradedBundle
        F s).degree) / finrank K E := by
  obtain ⟨b, a, c, hFa, hGc, _, _⟩ := NormFamily.exists_common_orthogonal_basis_ofTrivialFiltration
    F G hF hFbot hFtop hFleft hG hGbot hGtop hGleft
  have hrecover : (NormFamily.ofTrivialFiltration G hG hGbot hGtop hGleft).trivialFiltration
      (hξ := (NormFamily.ofTrivialFiltration_isUltrametricAtFinitePlaces G hG hGbot hGtop hGleft)) =
        G :=
    funext (NormFamily.trivialFiltration_ofTrivialFiltration G hG hGbot hGtop hGleft)
  have he := filtrationPairing_eq_finsum_graded_degree_of_common_basis
    (ofTrivialFiltration G hG hGbot hGtop hGleft)
    (hV := (NormFamily.ofTrivialFiltration_isUltrametricAtFinitePlaces G hG hGbot hGtop hGleft)) F
      hF b a c hFa
    (by simpa only [ofTrivialFiltration_toNormFamily, hrecover] using hGc)
  simpa only [ofTrivialFiltration_toNormFamily, hrecover] using he

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Hermitian
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HN
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Norm.CommonAdaptedBasis
public import ArakelovGeometry.LinearAlgebra.Filtration.Pairing

/-!
# Expectation and actual trivial-place degree

Exact degree additivity along the flag of literal norm balls computes the
degree from the dimensions and weights of its actual quotient factors.
-/

@[expose] public section

open Module

namespace ArakelovGeometry.AdelicVectorBundle

open AdelicStructure

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Compute the actual degree from a flag whose steps and strict predecessors
are literal norm balls. Every quotient carries the actual induced norm. -/
theorem degree_eq_sum_trivialFiltration_flag
    (V : AdelicVectorBundle (singleTrivialPlace K))
    [hS : (singleTrivialPlace K).HasMeasurableBase]
    [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametric]
    {n : ℕ} (U : Fin (n + 1) → Submodule K V) (a : Fin n → ℝ)
    (hU : Monotone U) (hz : U 0 = ⊥) (ht : U (Fin.last n) = ⊤)
    (hlevel : ∀ i, V.toNormFamily.trivialFiltration (a i) = U i.succ)
    (hright : ∀ i, (⨆ s : {s : ℝ // a i < s},
      V.toNormFamily.trivialFiltration s.val) = U i.castSucc) :
    V.degree = ∑ i : Fin n,
      a i * (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype) : ℝ) := by
  have hH : V.toNormFamily.IsHermitian := by
    refine ⟨hV, ?_⟩
    intro ω hω
    simp only [singleTrivialPlace_Ωinf, Set.mem_empty_iff_false] at hω
  rw [← V.sum_flagQuotient_degree_eq_of_isHermitian U hU hz ht (hV := hH)]
  apply Finset.sum_congr rfl
  intro i _
  have he := degree_eq_neg_finrank_mul_log_of_trivialSeminorm_eq_const
      (V.flagQuotientOfMeasurableBase U i)
      (Real.exp_pos (-a i))
      (V.toNormFamily.trivialSeminorm_subquotient_eq_exp_neg_of_ball_endpoints
         (U i.castSucc) (U i.succ) (a i) (hlevel i) (hright i))
  simpa only [Real.log_exp, neg_mul_neg, mul_comm] using he

/-- The degree of an arbitrary actual ultrametric norm at the trivial place is
the intrinsic dimension-weighted sum of its literal graded quotients. -/
theorem degree_eq_finsum_trivialFiltration
    (V : AdelicVectorBundle (singleTrivialPlace K))
    [hS : (singleTrivialPlace K).HasMeasurableBase]
    [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametric] :
    V.degree = ∑ᶠ t : ℝ,
      t * (finrank K (Submodule.FiltrationGraded (V.toNormFamily.trivialFiltration) t) : ℝ) := by
  obtain ⟨n, U, a, hU, hz, ht, _, ha, _, hlevel, hright, hrec⟩ :=
    V.toNormFamily.exists_strictMono_flag_and_jumps_trivialFiltration
  rw [V.degree_eq_sum_trivialFiltration_flag U a hU.monotone hz ht hlevel hright]
  exact (Submodule.finsum_weight_mul_finrank_filtrationGraded_eq_flag
    U a ha.injective hlevel hright hrec).symm

/-- The intrinsic expectation is the existing slope, not a new arithmetic slope. -/
theorem slope_eq_filtrationExpectation_trivialFiltration
    (V : AdelicVectorBundle (singleTrivialPlace K))
    [hS : (singleTrivialPlace K).HasMeasurableBase]
    [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsUltrametric] :
    V.slope = Submodule.filtrationExpectation (V.toNormFamily.trivialFiltration) := by
  rw [slope, degree_eq_finsum_trivialFiltration V, Submodule.filtrationExpectation]

/-- Every finite real filtration has finite support on the actual shared grade carrier.
The adapted basis is produced by the common-basis theorem, applied to `(F,F)`. -/
theorem finite_support_filtrationGraded (F : ℝ → Submodule K E)
    (hF : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    (Function.support (fun t ↦ finrank K (Submodule.FiltrationGraded F t))).Finite := by
  obtain ⟨b, a, _, hFa, _, _, _⟩ := Submodule.exists_common_weighted_basis
    hF hbot htop hleft hF hbot htop hleft
  exact Submodule.finite_support_finrank_filtrationGraded b a hFa

/-- The bundle attached to any source real filtration has its intrinsic expectation as slope. -/
theorem slope_ofTrivialFiltration_eq_expectation
    [hS : (singleTrivialPlace K).HasMeasurableBase]
    [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
    (F : ℝ → Submodule K E)
    (hF : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    (ofTrivialFiltration F hF hbot htop hleft).slope =
      Submodule.filtrationExpectation F := by
  have he := slope_eq_filtrationExpectation_trivialFiltration
      (ofTrivialFiltration F hF hbot htop hleft)
      (hV := (NormFamily.ofTrivialFiltration_isUltrametric F hF hbot htop hleft))
  have hrecover : (NormFamily.ofTrivialFiltration F hF hbot htop hleft).trivialFiltration
      (hξ := (NormFamily.ofTrivialFiltration_isUltrametric F hF hbot htop hleft)) = F :=
    funext (NormFamily.trivialFiltration_ofTrivialFiltration F hF hbot htop hleft)
  simpa only [ofTrivialFiltration_toNormFamily, hrecover] using he

/-- Arbitrary adapted-basis weights compute the actual slope of the associated bundle. -/
theorem slope_ofTrivialFiltration_eq_sum_weights
    [hS : (singleTrivialPlace K).HasMeasurableBase]
    [hN : (singleTrivialPlace K).IsArchimedeanNormalized]
    (F : ℝ → Submodule K E)
    (hF : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    {ι : Type*} [Fintype ι] (b : Basis ι K E) (a : ι → ℝ)
    (hb : ∀ t, F t = Submodule.span K (b '' {i | t ≤ a i})) :
    (ofTrivialFiltration F hF hbot htop hleft).slope =
      (∑ i, a i) / finrank K E := by
  rw [slope_ofTrivialFiltration_eq_expectation,
    Submodule.filtrationExpectation_eq_sum_weights b a hb]

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Optimal.Geometric
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Graded.Degree
public import ArakelovGeometry.LinearAlgebra.Filtration.RankDrop

/-!
# Slope comparison from binary Harder–Narasimhan variation

A centered negative pair produces a global optimizer, lifted Harder–Narasimhan
filtrations on its grades, common adapted bases, and strict decrease of the sum
of grade ranks. Upper and lower variation bounds for these same data compare
the quotient slope with the sum of the factor slopes. The quotient retains the
pushforward of the original orthogonal tensor norm.

The results assume semistable Hermitian factors over a proper adelic curve, with
the stated discrete or countable-density conditions. Tensor compatibility of Harder–Narasimhan
filtrations on all strictly smaller-rank grades is an explicit induction hypothesis.
The final theorem obtains the negative pair from geometric nonsemistability over
the original characteristic-zero field.

This is a conditional binary slope comparison in the setting of
[ChenMoriwaki2020], Chapter 5. It does not establish the general variational
inequality (5.13), and the smaller-rank hypothesis remains explicit.
-/

@[expose] public section

open Module Submodule
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u

section Conditional

variable {K : Type*} [Field K] {Q : Type*}
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]
  {S : AdelicStructure K} [S.IsProper]
  (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]

/-- For semistable Hermitian factors, a centered negative pair gives a lower bound
on the tensor quotient slope by the sum of the factor slopes. The optimizer,
lifted Harder–Narasimhan filtrations, common bases, and strict decrease of the
sum of grade ranks are constructed. Tensor compatibility on all strictly smaller-rank grades of the
fixed factors is assumed. The original quotient norm is retained. -/
theorem slope_sum_le_tensor_quotient_of_negative_candidate
    [hsemiV : V.IsMeanSlopeSemistable] [hsemiW : W.IsMeanSlopeSemistable]
    (q : V ⊗[K] W →ₗ[K] Q) (hq : Function.Surjective q) (hQ : 0 < finrank K Q)
    (hInd : ∀ (P : ℝ → Submodule K V) (R : ℝ → Submodule K W) (t u : ℝ),
      finrank K (FiltrationGraded P t) + finrank K (FiltrationGraded R u) <
        finrank K V + finrank K W →
      (tensorFiltrationGradedSource V W P R t u).hermitianHNFiltration
        (hV := (tensorFiltrationGradedSource_isHermitian V W P R t u)) =
      tensorFiltration
        ((V.filtrationGraded P t).hermitianHNFiltration (hV := (hV.filtrationGraded P t)))
        ((W.filtrationGraded R u).hermitianHNFiltration (hV := (hW.filtrationGraded R u))))
    (P₀ : ℝ → Submodule K V) (R₀ : ℝ → Submodule K W)
    (hP₀ : Antitone P₀ ∧ (∃ t, P₀ t = ⊥) ∧ (∃ t, P₀ t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P₀ s = P₀ t) ∧
      filtrationExpectation P₀ = 0)
    (hR₀ : Antitone R₀ ∧ (∃ t, R₀ t = ⊥) ∧ (∃ t, R₀ t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → R₀ s = R₀ t) ∧
      filtrationExpectation R₀ = 0)
    (hneg₀ : filtrationExpectation (fun t ↦ (tensorFiltration P₀ R₀ t).map q) < 0) :
    let T := V.orthogonalTensorPair W
    let B := T.pushforward q hq (hm := (T.isMeasurable.pushforward_of_discrete_or_countable q hq))
    V.slope + W.slope ≤ B.slope := by
  obtain ⟨P, R, hP, hR, hunit, _, _, L, M, b, c, a, r, d, s,
      hPb, hL, hRc, hM, hlower⟩ :=
    exists_bost_hn_variation_bound V W q hq hQ
      P₀ R₀ hP₀ hR₀ hneg₀
  have hsmall (t u : ℝ) :
      finrank K (FiltrationGraded P t) + finrank K (FiltrationGraded R u) <
        finrank K V + finrank K W :=
    finrank_filtrationGraded_add_lt_of_centered b c a d hPb hRc
      hP.2.2.2.2 hR.2.2.2.2 (by rw [hunit]; exact one_ne_zero) t u
  obtain ⟨hδ, hupper⟩ := tensorFiltrationQuotient_eventual_hn_upper V W
    q hq hP.1 hR.1 b c a d hPb hRc L M r s hL hM
      (fun i j ↦ hsmall (a i) (d j)) (hInd P R)
  exact (hlower _ hupper).trans hδ

end Conditional

section Geometric

open ArakelovGeometry.InvariantTheory

variable {K E F Q : Type u} [Field K] [CharZero K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Nontrivial Q]
  {S : AdelicStructure K} [S.IsProper]
  (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
  [Nontrivial V] [Nontrivial W]
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]

/-- For semistable Hermitian factors, geometric nonsemistability of the quotient
bounds its slope below by the sum of the factor slopes, assuming tensor compatibility of
Harder–Narasimhan filtrations on all strictly smaller-rank grades.
The original tensor pushforward quotient norm, proper adelic curve, and stated
discrete or countable-density conditions are retained, including trivial valuations.
This is a conditional binary comparison; the full inequality (5.13) of
[ChenMoriwaki2020] is not asserted. -/
theorem slope_sum_le_tensor_quotient_of_not_geometricallySemistable
    [hsemiV : V.IsMeanSlopeSemistable] [hsemiW : W.IsMeanSlopeSemistable]
    (q : V ⊗[K] W →ₗ[K] Q) (hq : Function.Surjective q) (hQ : 0 < finrank K Q)
    (hInd : ∀ (P : ℝ → Submodule K V) (R : ℝ → Submodule K W) (t u : ℝ),
      finrank K (FiltrationGraded P t) + finrank K (FiltrationGraded R u) <
        finrank K V + finrank K W →
      (tensorFiltrationGradedSource V W P R t u).hermitianHNFiltration
        (hV := (tensorFiltrationGradedSource_isHermitian V W P R t u)) =
      tensorFiltration
        ((V.filtrationGraded P t).hermitianHNFiltration (hV := (hV.filtrationGraded P t)))
        ((W.filtrationGraded R u).hermitianHNFiltration (hV := (hW.filtrationGraded R u))))
    (hns : ¬ IsGeometricallySemistableTensorQuotient (LiftedBoolTensorFactors V W)
      (q.comp (boolTensorPairEquiv K V W).toLinearMap)) :
    let T := V.orthogonalTensorPair W
    let B := T.pushforward q hq (hm := (T.isMeasurable.pushforward_of_discrete_or_countable q hq))
    V.slope + W.slope ≤ B.slope := by
  obtain ⟨P₀, R₀, hP₀, hR₀, _, hneg₀, _⟩ :=
    exists_normalized_tensor_quotient_optimizer_of_not_geometricallySemistable q hq hQ hns
  exact slope_sum_le_tensor_quotient_of_negative_candidate V W
     q hq hQ hInd P₀ R₀ hP₀ hR₀ hneg₀

end Geometric

end ArakelovGeometry.AdelicVectorBundle

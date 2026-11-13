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
# Bost's actual HN variation assembly

This is the binary unstable-case slope step on Bost pages 31–32, equation (47).
An actual original-field centered negative candidate produces the optimizer,
actual grade-HN lifts, common adapted bases and strict rank-sum drop. The A6
eventual upper bound and A9 lower bound are applied to those same chosen data.
The quotient retains the pushforward of the original orthogonal tensor norm.

Smaller-rank tensor-HN compatibility is a quantified induction hypothesis on
all actual grades of the fixed factors, including those chosen after optimization.
Rank drop makes this hypothesis applicable; it does not prove it. The one-sided
variation bound suffices, so neither the full CM (5.13), the exact affine identity,
the entire Bost Theorem 1.1 nor its separate Section 6 branch is asserted.
The proper adelic, discrete-or-countable and Hermitian norm context is retained.
The final theorem obtains the candidate from the actual A2 geometric instability
hypothesis over the original characteristic-zero field, leaving only the genuine
smaller-rank tensor-HN induction boundary.
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

/-- The Bost pp.31–32 quotient slope bound from an ACTUAL negative pair. The optimizer,
HN lifts and common bases are constructed, and the strict rank-sum drop is derived.
The only arithmetic induction boundary is tensor-HN compatibility on all smaller-rank
actual grades of the fixed factors, quantified before choosing the optimizer. A6's
one-sided upper bound on the same data suffices; full CM (5.13) is not asserted.
The original quotient norm is retained. Geometric production of the candidate is separate. -/
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

/-- The actual geometric unstable case of Bost pp.31–32, equation (47), with the
genuine smaller-rank tensor-HN induction hypothesis still explicit. A2 geometric
nonsemistability produces an original-field unit negative global optimizer; its
actual candidate enters the proved optimizer/HN-lift arithmetic assembly. There
is no assumed numerical inequality or rank-drop certificate. The original tensor
pushforward quotient norm, proper adelic and discrete-or-countable setting are
retained, including trivial valuations. Only the binary HN variation is needed;
full CM (5.13), the full HN induction, Section 6 and Bost Theorem 1.1 are not asserted. -/
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

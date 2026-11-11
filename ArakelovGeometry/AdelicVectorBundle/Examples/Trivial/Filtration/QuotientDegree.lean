/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.Optimization
public import ArakelovGeometry.LinearAlgebra.Filtration.Lift
public import ArakelovGeometry.LinearAlgebra.Filtration.Tensor
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Expectation
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Quotient
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Tensor

/-!
# The actual quotient filtration as a finite determinant maximum

The image filtration is the literal filtration of the actual quotient norm.
Its expectation is the largest nonzero determinant-coordinate weight divided
by the quotient dimension.
-/

@[expose] public section

open Module
open scoped BigOperators

namespace Submodule

variable {K E Q ι : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup Q] [Module K Q]
  [FiniteDimensional K Q] [Finite ι]

/-- Every actual quotient of a weighted basis has an adapted target basis.
The four real-filtration properties are derived from the source weights. -/
theorem exists_weighted_basis_image (b : Basis ι K E) (w : ι → ℝ)
    (q : E →ₗ[K] Q) (hq : Function.Surjective q) :
    ∃ (c : Basis (Fin (finrank K Q)) K Q) (d : Fin (finrank K Q) → ℝ),
      ∀ t, (span K (b '' {i | t ≤ w i})).map q =
        span K (c '' {k | t ≤ d k}) := by
  let G := fun t ↦ (span K (b '' {i | t ≤ w i})).map q
  have ha : Antitone G := fun s t hst ↦ map_mono (antitone_span_weights b w hst)
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := span_weights_attains_bot_top b w
  have hb : ∃ t, G t = ⊥ := ⟨s, by simp [G, hs]⟩
  have he : ∃ t, G t = ⊤ := ⟨t, by simp [G, ht, LinearMap.range_eq_top.mpr hq]⟩
  have hl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → G s = G t := by
    intro t
    obtain ⟨ε, hε, hh⟩ := span_weights_locallyConstant_left b w t
    exact ⟨ε, hε, fun s hs hst ↦ congrArg (map q) (hh s hs hst)⟩
  obtain ⟨c, d, _, hc, _⟩ := exists_common_weighted_basis ha hb he hl ha hb he hl
  exact ⟨c, d, hc⟩

/-- The actual quotient expectation is an attained maximum of determinant
weight sums divided by dimension. The target reference basis is arbitrary. -/
theorem exists_quotient_expectation_maximum (b : Basis ι K E) (w : ι → ℝ)
    (c : Basis (Fin (finrank K Q)) K Q) (q : E →ₗ[K] Q)
    (hq : Function.Surjective q) :
    ∃ σ ∈ quotientDeterminantSupport b c q,
      filtrationExpectation (fun t ↦ (span K (b '' {i | t ≤ w i})).map q) =
        (∑ k, w (σ k)) / finrank K Q ∧
      ∀ τ ∈ quotientDeterminantSupport b c q, (∑ k, w (τ k)) ≤ ∑ k, w (σ k) := by
  obtain ⟨c', d, hc'⟩ := exists_weighted_basis_image b w q hq
  obtain ⟨σ, hσ, he, hmax⟩ := exists_maximal_quotient_weight_of_adapted b c' q w d hc'
  have hs := quotientDeterminantSupport_basis_independent b c c' q
  refine ⟨σ, hs.symm ▸ hσ, ?_, ?_⟩
  · rw [filtrationExpectation_eq_sum_weights c' d hc', he]
  · intro τ hτ
    rw [he]
    exact hmax τ (hs ▸ hτ)

/-- Surjectivity guarantees an actual nonzero determinant coordinate. -/
theorem quotientDeterminantSupport_nonempty (b : Basis ι K E)
    (c : Basis (Fin (finrank K Q)) K Q) (q : E →ₗ[K] Q)
    (hq : Function.Surjective q) : (quotientDeterminantSupport b c q).Nonempty := by
  obtain ⟨σ, hσ, _⟩ := exists_quotient_expectation_maximum b (fun _ ↦ 0) c q hq
  exact ⟨σ, hσ⟩

/-- The finite maximum formula for the actual image filtration, with the
quotient dimension in the denominator. -/
theorem filtrationExpectation_image_eq_sup' (b : Basis ι K E) (w : ι → ℝ)
    (c : Basis (Fin (finrank K Q)) K Q) (q : E →ₗ[K] Q)
    (hq : Function.Surjective q) :
    filtrationExpectation (fun t ↦ (span K (b '' {i | t ≤ w i})).map q) =
      (quotientDeterminantSupport b c q).sup'
        (quotientDeterminantSupport_nonempty b c q hq) (fun σ ↦ ∑ k, w (σ k)) /
          finrank K Q := by
  obtain ⟨σ, hσ, he, hmax⟩ := exists_quotient_expectation_maximum b w c q hq
  rw [he]
  congr 1
  apply le_antisymm
  · exact Finset.le_sup' (fun τ ↦ ∑ k, w (τ k)) hσ
  · exact Finset.sup'_le _ _ hmax

end Submodule

namespace ArakelovGeometry.NormFamily

open AdelicStructure Submodule
open scoped TensorProduct

variable {K J Q : Type*} [Field K] [Fintype J]
  {E : J → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)]
  [∀ j, FiniteDimensional K (E j)]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]
  {ι : J → Type*} [∀ j, Finite (ι j)]

/-- The actual finite epsilon tensor norm and its actual quotient have exactly
the determinant maximum of the original prescribed factor weights. -/
theorem filtrationExpectation_pushforward_injectiveTensor_eq_sup'
    (ν : ∀ j, NormFamily (singleTrivialPlace K) (E j))
    (hν : ∀ j, (ν j).IsUltrametric) (b : ∀ j, Basis (ι j) K (E j))
    (w : ∀ j, ι j → ℝ)
    (hb : ∀ j t, (ν j).trivialFiltration (hν j) t = span K (b j '' {i | t ≤ w j i}))
    (c : Basis (Fin (finrank K Q)) K Q) (q : (⨂[K] j, E j) →ₗ[K] Q)
    (hq : Function.Surjective q) :
    filtrationExpectation (((injectiveTensor ν).pushforward q hq).trivialFiltration
      ((injectiveTensor_isUltrametric ν).pushforward q hq)) =
      (quotientDeterminantSupport (Basis.piTensorProduct b) c q).sup'
        (quotientDeterminantSupport_nonempty (Basis.piTensorProduct b) c q hq)
        (fun σ ↦ ∑ k, ∑ j, w j (σ k j)) / finrank K Q := by
  have he : ((injectiveTensor ν).pushforward q hq).trivialFiltration
      ((injectiveTensor_isUltrametric ν).pushforward q hq) = fun t ↦
      (span K (Basis.piTensorProduct b '' {p | t ≤ ∑ j, w j (p j)})).map q := by
    funext t
    rw [trivialFiltration_pushforward _ (injectiveTensor_isUltrametric ν),
      trivialFiltration_injectiveTensor_eq_span_of_weights ν b hν w hb]
  rw [he]
  exact filtrationExpectation_image_eq_sup' (Basis.piTensorProduct b)
    (fun p ↦ ∑ j, w j (p j)) c q hq

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NormFamily

open AdelicStructure Submodule

variable {K E Q ι : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup Q] [Module K Q]
  [FiniteDimensional K E] [FiniteDimensional K Q] [Finite ι]

/-- The determinant maximum computes the literal filtration expectation of
the actual quotient norm, using any basis adapted to the source norm. -/
theorem filtrationExpectation_pushforward_eq_sup'
    (ξ : NormFamily (singleTrivialPlace K) E) (hξ : ξ.IsUltrametric)
    (b : Basis ι K E) (w : ι → ℝ)
    (hb : ∀ t, ξ.trivialFiltration hξ t = span K (b '' {i | t ≤ w i}))
    (c : Basis (Fin (finrank K Q)) K Q) (q : E →ₗ[K] Q)
    (hq : Function.Surjective q) :
    filtrationExpectation ((ξ.pushforward q hq).trivialFiltration (hξ.pushforward q hq)) =
      (quotientDeterminantSupport b c q).sup'
        (quotientDeterminantSupport_nonempty b c q hq) (fun σ ↦ ∑ k, w (σ k)) /
          finrank K Q := by
  have he : (ξ.pushforward q hq).trivialFiltration (hξ.pushforward q hq) =
      fun t ↦ (span K (b '' {i | t ≤ w i})).map q := by
    funext t
    rw [trivialFiltration_pushforward ξ hξ q hq, hb]
  rw [he]
  exact filtrationExpectation_image_eq_sup' b w c q hq

end ArakelovGeometry.NormFamily

namespace Submodule

open scoped TensorProduct

variable {K J Q : Type*} [Field K] [Fintype J]
  {E : J → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]
  {ι : J → Type*} [∀ j, Finite (ι j)]

/-- For a finite family, the actual quotient of the intrinsic tensor
filtration has a finite maximum over its realized determinant support. -/
theorem filtrationExpectation_piTensor_image_eq_sup'
    (b : ∀ j, Basis (ι j) K (E j)) (w : ∀ j, ι j → ℝ)
    {F : ∀ j, ℝ → Submodule K (E j)}
    (hF : ∀ j t, F j t = span K (b j '' {i | t ≤ w j i}))
    (c : Basis (Fin (finrank K Q)) K Q) (q : (⨂[K] j, E j) →ₗ[K] Q)
    (hq : Function.Surjective q) :
    filtrationExpectation (fun t ↦ (piTensorFiltration F t).map q) =
      (quotientDeterminantSupport (Basis.piTensorProduct b) c q).sup'
        (quotientDeterminantSupport_nonempty (Basis.piTensorProduct b) c q hq)
        (fun σ ↦ ∑ k, ∑ j, w j (σ k j)) / finrank K Q := by
  have he : (fun t ↦ (piTensorFiltration F t).map q) =
      fun t ↦ (span K (Basis.piTensorProduct b '' {p | t ≤ ∑ j, w j (p j)})).map q := by
    funext t
    rw [piTensorFiltration_eq_span b w hF]
  rw [he]
  exact filtrationExpectation_image_eq_sup' (Basis.piTensorProduct b)
    (fun p ↦ ∑ j, w j (p j)) c q hq

end Submodule

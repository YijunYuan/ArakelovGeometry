/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Expectation
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Quotient
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Tensor
public import ArakelovGeometry.LinearAlgebra.Filtration.Lift
public import ArakelovGeometry.LinearAlgebra.Filtration.Optimization
public import ArakelovGeometry.LinearAlgebra.Filtration.Tensor

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
    [hν : ∀ j, (ν j).IsUltrametric] (b : ∀ j, Basis (ι j) K (E j))
    (w : ∀ j, ι j → ℝ)
    (hb : ∀ j t, (ν j).trivialFiltration (hξ := (hν j)) t = span K (b j '' {i | t ≤ w j i}))
    (c : Basis (Fin (finrank K Q)) K Q) (q : (⨂[K] j, E j) →ₗ[K] Q)
    (hq : Function.Surjective q) :
    filtrationExpectation (((injectiveTensor ν).pushforward q hq).trivialFiltration
      (hξ := ((injectiveTensor_isUltrametric ν).pushforward q hq))) =
      (quotientDeterminantSupport (Basis.piTensorProduct b) c q).sup'
        (quotientDeterminantSupport_nonempty (Basis.piTensorProduct b) c q hq)
        (fun σ ↦ ∑ k, ∑ j, w j (σ k j)) / finrank K Q := by
  have he : ((injectiveTensor ν).pushforward q hq).trivialFiltration
      (hξ := ((injectiveTensor_isUltrametric ν).pushforward q hq)) = fun t ↦
      (span K (Basis.piTensorProduct b '' {p | t ≤ ∑ j, w j (p j)})).map q := by
    funext t
    rw [trivialFiltration_pushforward _ (hξ := (injectiveTensor_isUltrametric ν)),
      trivialFiltration_injectiveTensor_eq_span_of_weights ν b w hb]
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
    (ξ : NormFamily (singleTrivialPlace K) E) [hξ : ξ.IsUltrametric]
    (b : Basis ι K E) (w : ι → ℝ)
    (hb : ∀ t, ξ.trivialFiltration t = span K (b '' {i | t ≤ w i}))
    (c : Basis (Fin (finrank K Q)) K Q) (q : E →ₗ[K] Q)
    (hq : Function.Surjective q) :
    filtrationExpectation ((ξ.pushforward q hq).trivialFiltration (hξ := (hξ.pushforward q hq))) =
      (quotientDeterminantSupport b c q).sup'
        (quotientDeterminantSupport_nonempty b c q hq) (fun σ ↦ ∑ k, w (σ k)) /
          finrank K Q := by
  have he : (ξ.pushforward q hq).trivialFiltration (hξ := (hξ.pushforward q hq)) =
      fun t ↦ (span K (b '' {i | t ≤ w i})).map q := by
    funext t
    rw [trivialFiltration_pushforward ξ q hq, hb]
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

namespace Submodule

open scoped TensorProduct
open ArakelovGeometry

section BinaryTransport

variable {K : Type*} [Field K] {E : Unit ⊕ Unit → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

/-- The canonical binary equivalence carries the actual finite convolution
onto the actual ordinary tensor-product convolution, at every threshold. -/
theorem piTensorFiltration_map_binaryTensorEquiv
    (F : ∀ i, ℝ → Submodule K (E i)) (γ : ℝ) :
    (piTensorFiltration F γ).map (binaryTensorEquiv K E).toLinearMap =
      tensorFiltration (F (.inl ())) (F (.inr ())) γ := by
  classical
  apply le_antisymm
  · rw [piTensorFiltration, map_iSup]
    apply iSup_le
    intro t
    rw [map_iSup]
    apply iSup_le
    intro ht
    rw [PiTensorProduct.mapIncl, PiTensorProduct.map_range_eq_span_tprod, map_span]
    apply span_le.mpr
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    simp only [LinearEquiv.coe_coe, binaryTensorEquiv_tprod]
    apply tmul_mem_tensorFiltration _ (x (.inl ())).property (x (.inr ())).property
    simpa only [Fintype.sum_sum_type, Fintype.sum_unique] using ht
  · apply iSup_le
    intro t
    apply iSup_le
    intro u
    apply iSup_le
    intro htu
    rintro _ ⟨z, rfl⟩
    induction z with
    | tmul x y =>
      let s : Unit ⊕ Unit → ℝ := Sum.elim (fun _ ↦ t) (fun _ ↦ u)
      let v : ∀ i, E i := fun i ↦ match i with
        | .inl _ => x.val
        | .inr _ => y.val
      refine ⟨⨂ₜ[K] i, v i, ?_, ?_⟩
      · apply tprod_mem_piTensorFiltration (t := s)
        · simpa [s, Fintype.sum_sum_type] using htu
        · rintro (⟨⟩ | ⟨⟩)
          · exact x.property
          · exact y.property
      · simp [v]
    | add x y hx hy => simpa only [map_add] using add_mem hx hy

end BinaryTransport

section BinaryMaximum

variable {K E V Q ι κ : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup V] [Module K V]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Finite ι] [Finite κ]

/-- The ordinary binary quotient has the same actual determinant maximum,
with the two original weights added and with the quotient-rank denominator. -/
theorem filtrationExpectation_tensor_image_eq_sup'
    (b : Basis ι K E) (c : Basis κ K V) (w : ι → ℝ) (z : κ → ℝ)
    {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ w i}))
    (hG : ∀ t, G t = span K (c '' {i | t ≤ z i}))
    (d : Basis (Fin (finrank K Q)) K Q) (q : E ⊗[K] V →ₗ[K] Q)
    (hq : Function.Surjective q) :
    filtrationExpectation (fun t ↦ (tensorFiltration F G t).map q) =
      (quotientDeterminantSupport (b.tensorProduct c) d q).sup'
        (quotientDeterminantSupport_nonempty (b.tensorProduct c) d q hq)
        (fun σ ↦ ∑ k, (w (σ k).1 + z (σ k).2)) / finrank K Q := by
  simp_rw [tensorFiltration_eq_span_tensorProduct b c w z hF hG]
  exact filtrationExpectation_image_eq_sup' (b.tensorProduct c) _ d q hq

end BinaryMaximum

end Submodule

namespace ArakelovGeometry.NormFamily

open AdelicStructure Submodule
open scoped TensorProduct

universe u

variable {K Q ι κ : Type*} [Field K] {E V : Type u}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Finite ι] [Finite κ]

/-- The literal ordinary binary epsilon quotient norm has the determinant
maximum of the prescribed original factor weights. -/
theorem filtrationExpectation_pushforward_injectiveTensorPair_eq_sup'
    (ξ : NormFamily (singleTrivialPlace K) E) (η : NormFamily (singleTrivialPlace K) V)
    [hξ : ξ.IsUltrametric] [hη : η.IsUltrametric]
    (b : Basis ι K E) (c : Basis κ K V) (w : ι → ℝ) (z : κ → ℝ)
    (hb : ∀ t, ξ.trivialFiltration t = span K (b '' {i | t ≤ w i}))
    (hc : ∀ t, η.trivialFiltration t = span K (c '' {i | t ≤ z i}))
    (d : Basis (Fin (finrank K Q)) K Q) (q : E ⊗[K] V →ₗ[K] Q)
    (hq : Function.Surjective q) :
    filtrationExpectation (((ξ.injectiveTensorPair η).pushforward q hq).trivialFiltration
      (hξ := ((ξ.injectiveTensorPair_isUltrametric η).pushforward q hq))) =
      (quotientDeterminantSupport (b.tensorProduct c) d q).sup'
        (quotientDeterminantSupport_nonempty (b.tensorProduct c) d q hq)
        (fun σ ↦ ∑ k, (w (σ k).1 + z (σ k).2)) / finrank K Q := by
  have hspan (t : ℝ) :
      (ξ.injectiveTensorPair η).trivialFiltration
          (hξ := (ξ.injectiveTensorPair_isUltrametric η)) t =
        span K (b.tensorProduct c '' {ij | t ≤ w ij.1 + z ij.2}) := by
    rw [trivialFiltration_injectiveTensorPair ξ η]
    exact tensorFiltration_eq_span_tensorProduct b c w z hb hc t
  exact filtrationExpectation_pushforward_eq_sup' (ξ.injectiveTensorPair η)
    (hξ := (ξ.injectiveTensorPair_isUltrametric η)) (b.tensorProduct c)
    (fun ij ↦ w ij.1 + z ij.2) hspan d q hq

end ArakelovGeometry.NormFamily

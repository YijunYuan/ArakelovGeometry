/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.ScalarExtension
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Optimal

/-!
# Rationality of an actual centered negative binary pair

For the binary Bost application on page 31 of `bost.pdf`, an actual negative
centered pair over an algebraic algebraically closed extension descends to such
a pair over the original characteristic-zero field. Real weights and total
energy one are retained. The input pair need not be Galois invariant: the
conditional unique optimizer over the extension field produces stable layers.

The internal finite-family optimization is reused only to prove this binary
rationality input. Global optimality of the descended pair is not needed, and
geometric instability producing a negative input remains a separate theorem.
The extension need not have finite degree; no number-field assumption is used.
Actual subspace/image filtrations have the completed trivial-place meanings
proved by the existing norm/filtration bridges.
-/

@[expose] public section

open Module ArakelovGeometry ArakelovGeometry.HermitianAbsoluteDescent
open scoped TensorProduct

namespace Submodule

section StableOptimizer

variable {K L J Q : Type*} [Field K] [Field L] [Algebra K L] [Fintype J]
  {E : J → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)]
  [∀ j, FiniteDimensional K (E j)]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

set_option quotPrecheck false in
local notation "Families" => (∀ j, ℝ → Submodule L (L ⊗[K] E j))
set_option quotPrecheck false in
local notation "Admissible" => (fun F : Families ↦ ∀ j,
  Antitone (F j) ∧ (∃ t, F j t = ⊥) ∧ (∃ t, F j t = ⊤) ∧
  (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F j s = F j t) ∧
  filtrationExpectation (F j) = 0)
set_option quotPrecheck false in
local notation "Energy" => (fun F : Families ↦ ∑ j, filtrationPairing (F j) (F j))

variable (q : (⨂[K] j, E j) →ₗ[K] Q) (hq : Function.Surjective q)

set_option quotPrecheck false in
local notation "Value" => (fun F : Families ↦
  filtrationExpectation (fun t ↦ (piTensorFiltration F t).map (piTensorQuotientBaseChange q)))

include hq

/-- An arbitrary actual centered negative input over the extension field produces
Galois-stable actual layers. Stability is proved from uniqueness of the global
unit optimizer, by pulling every comparison family back by the inverse automorphism.
This finite-family producer is used internally by the binary Bost descent. -/
theorem exists_galois_stable_normalized_negative_family
    (ha : ∀ j, 0 < finrank K (E j)) (F₀ : Families)
    (hF₀ : Admissible F₀) (hneg₀ : Value F₀ < 0) :
    ∃ P : Families, Admissible P ∧ Energy P = 1 ∧ Value P < 0 ∧
      ∀ j t (σ : L ≃ₐ[K] L) (x : L ⊗[K] E j), x ∈ P j t →
        scalarExtensionSemilinearEquiv σ x ∈ P j t := by
  let act (σ : L ≃ₐ[K] L) (F : Families) : Families :=
    fun j t ↦ scalarExtensionSubspaceOrderIso σ (F j t)
  have hA (σ : L ≃ₐ[K] L) (F : Families) (hF : Admissible F) : Admissible (act σ F) := by
    intro j
    obtain ⟨hm, hb, ht, hl⟩ := finite_filtration_scalarExtensionSubspaceOrderIso σ (F j)
      (hF j).1 (hF j).2.1 (hF j).2.2.1 (hF j).2.2.2.1
    refine ⟨hm, hb, ht, hl, ?_⟩
    exact (filtrationExpectation_scalarExtensionSubspaceOrderIso σ (F j)).trans (hF j).2.2.2.2
  have hE (σ : L ≃ₐ[K] L) (F : Families) : Energy (act σ F) = Energy F := by
    exact Finset.sum_congr rfl fun j _ ↦ filtrationPairing_scalarExtensionSubspaceOrderIso σ _ _
  have hV (σ : L ≃ₐ[K] L) (F : Families) : Value (act σ F) = Value F :=
    filtrationExpectation_piTensor_image_galois σ q F
  obtain ⟨P, ⟨hP, hPE, hneg, hmin⟩, hunique⟩ :=
    exists_unique_normalized_quotient_optimizer (piTensorQuotientBaseChange (L := L) q)
      (piTensorQuotientBaseChange_surjective q hq)
      (fun j ↦ by simpa only [Module.finrank_baseChange] using ha j) F₀ hF₀ hneg₀
  refine ⟨P, hP, hPE, hneg, ?_⟩
  intro j t σ x hx
  have he : act σ P = P := by
    apply hunique
    refine ⟨hA σ P hP, (hE σ P).trans hPE, (hV σ P) ▸ hneg, ?_⟩
    intro F hF hpos
    have hh := hmin (act σ.symm F) (hA σ.symm F hF) ((hE σ.symm F).symm ▸ hpos)
    rw [hV, hE] at hh
    rw [hV]
    exact hh
  have hl : scalarExtensionSubspaceOrderIso σ (P j t) = P j t :=
    congrArg (fun H : Families ↦ H j t) he
  rw [← hl]
  exact ⟨x, hx, rfl⟩

end StableOptimizer

section DescendLayers

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [CharZero K] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual rational inverse images of stable finite-filtration layers form a
finite real filtration over the original characteristic-zero field. Infinite
Galois descent supplies layer equality; no finite-degree assumption is made. -/
theorem finite_filtration_rationalPart
    (F : ℝ → Submodule L (L ⊗[K] E))
    (hF : Antitone F) (hb : ∃ t, F t = ⊥) (ht : ∃ t, F t = ⊤)
    (hl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hstable : ∀ t (σ : L ≃ₐ[K] L) (x : L ⊗[K] E), x ∈ F t →
      scalarExtensionSemilinearEquiv σ x ∈ F t) :
    (∀ t, (rationalPart (F t)).baseChange L = F t) ∧
      Antitone (fun t ↦ rationalPart (F t)) ∧
      (∃ t, rationalPart (F t) = ⊥) ∧ (∃ t, rationalPart (F t) = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → rationalPart (F s) = rationalPart (F t)) := by
  have he t := baseChange_rationalPart_eq_of_stable_of_isAlgClosed (F t) (hstable t)
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    apply (baseChangeOrderEmbedding K E L).le_iff_le.mp
    change (rationalPart (F t)).baseChange L ≤ (rationalPart (F s)).baseChange L
    rw [he, he]
    exact hF hst
  · obtain ⟨t, ht⟩ := hb
    exact ⟨t, baseChange_injective (A := L) (by rw [he, ht, baseChange_bot])⟩
  · obtain ⟨t, ht⟩ := ht
    exact ⟨t, baseChange_injective (A := L) (by rw [he, ht, baseChange_top])⟩
  · intro t
    obtain ⟨ε, hε, heq⟩ := hl t
    exact ⟨ε, hε, fun s hs hst ↦ congrArg rationalPart (heq s hs hst)⟩

end DescendLayers

end Submodule

namespace Submodule

section BinaryBaseChange

universe u

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {E V : Type u} {Q : Type*}
  [AddCommGroup E] [Module K E] [AddCommGroup V] [Module K V]
  [AddCommGroup Q] [Module K Q]

/-- The ordinary binary scalar-extended quotient, using the canonical tensor base change. -/
noncomputable def tensorQuotientBaseChange (q : E ⊗[K] V →ₗ[K] Q) :
    (L ⊗[K] E) ⊗[L] (L ⊗[K] V) →ₗ[L] L ⊗[K] Q :=
  (q.baseChange L).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange K L E V).symm.toLinearMap

/-- The internal two-factor quotient is exactly the ordinary binary quotient base change.
This is compatibility of the prescribed maps, rather than a replacement quotient. -/
theorem piTensorQuotientBaseChange_binary (q : E ⊗[K] V →ₗ[K] Q) :
    piTensorQuotientBaseChange (L := L)
      (q.comp (binaryTensorEquiv K (BinaryTensorFactors E V)).toLinearMap) =
    (tensorQuotientBaseChange q).comp
      (binaryTensorEquiv L (fun i ↦ L ⊗[K] BinaryTensorFactors E V i)).toLinearMap := by
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := (tensorBaseChangeEquiv K L (BinaryTensorFactors E V)).surjective z
  simp only [piTensorQuotientBaseChange, tensorQuotientBaseChange, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have he := DFunLike.congr_fun (tensorBaseChangeEquiv_binary K L E V) y
  change binaryTensorEquiv L (fun i ↦ L ⊗[K] BinaryTensorFactors E V i)
      (tensorBaseChangeEquiv K L (BinaryTensorFactors E V) y) =
    TensorProduct.AlgebraTensorModule.distribBaseChange K L E V
      ((binaryTensorEquiv K (BinaryTensorFactors E V)).toLinearMap.baseChange L y) at he
  rw [he, LinearEquiv.symm_apply_apply, LinearMap.baseChange_comp]
  rfl

/-- The binary and internal finite-family objectives have identical actual quotient layers. -/
theorem piTensor_image_binary_baseChange
    (q : E ⊗[K] V →ₗ[K] Q)
    (F : ∀ i, ℝ → Submodule L (L ⊗[K] BinaryTensorFactors E V i)) (t : ℝ) :
    (piTensorFiltration F t).map (piTensorQuotientBaseChange (L := L)
      (q.comp (binaryTensorEquiv K (BinaryTensorFactors E V)).toLinearMap)) =
    (tensorFiltration (F (.inl ())) (F (.inr ())) t).map (tensorQuotientBaseChange q) := by
  rw [piTensorQuotientBaseChange_binary, map_comp, piTensorFiltration_map_binaryTensorEquiv]

end BinaryBaseChange

end Submodule

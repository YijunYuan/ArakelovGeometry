/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Optimal.Basic
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.ScalarExtension

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

private theorem tensorBaseChangeEquiv_binaryFactors :
    (binaryTensorEquiv L (fun i ↦ L ⊗[K] BinaryTensorFactors E V i)).toLinearMap ∘ₗ
      (tensorBaseChangeEquiv K L (BinaryTensorFactors E V)).toLinearMap =
    (TensorProduct.AlgebraTensorModule.distribBaseChange K L E V).toLinearMap ∘ₗ
      (binaryTensorEquiv K (BinaryTensorFactors E V)).toLinearMap.baseChange L := by
  apply LinearMap.restrictScalars_injective K
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change binaryTensorEquiv L (fun i ↦ L ⊗[K] BinaryTensorFactors E V i)
      (tensorBaseChangeEquiv K L (BinaryTensorFactors E V) (a ⊗ₜ[K] (⨂ₜ[K] i, x i))) =
    TensorProduct.AlgebraTensorModule.distribBaseChange K L E V
      ((binaryTensorEquiv K (BinaryTensorFactors E V)).toLinearMap.baseChange L
        (a ⊗ₜ[K] (⨂ₜ[K] i, x i)))
  simp only [tensorBaseChangeEquiv_tmul_tprod, map_smul, binaryTensorEquiv_tprod,
    LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]

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
  have he := DFunLike.congr_fun
    (tensorBaseChangeEquiv_binaryFactors (K := K) (L := L) (E := E) (V := V)) y
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

namespace Submodule

section BinaryRationality

universe u

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [CharZero K] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
  {E V : Type u} {Q : Type*}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- Binary rationality needed on page 31 of `bost.pdf`: any actual centered negative
pair for the scalar extension of a surjective positive-rank quotient produces an
actual centered negative pair over the original characteristic-zero field, with
unit total self-pairing. The extension is algebraic and algebraically closed,
possibly of infinite degree; weights remain real. Galois invariance is derived
from the unique global optimizer over `L`, and is not an input. This locally
proves the rationality auxiliary step for the binary Bost application using the
conditional CM optimization argument. Geometric instability producing negativity
and the variational inequality are
not assumed or proved here, and descended global optimality is not asserted. -/
theorem exists_centered_negative_tensor_filtrations_of_baseChange
    (q : E ⊗[K] V →ₗ[K] Q) (hq : Function.Surjective q) (hQ : 0 < finrank K Q)
    (F₀ : ℝ → Submodule L (L ⊗[K] E)) (G₀ : ℝ → Submodule L (L ⊗[K] V))
    (hF₀ : Antitone F₀ ∧ (∃ t, F₀ t = ⊥) ∧ (∃ t, F₀ t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F₀ s = F₀ t) ∧
      filtrationExpectation F₀ = 0)
    (hG₀ : Antitone G₀ ∧ (∃ t, G₀ t = ⊥) ∧ (∃ t, G₀ t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → G₀ s = G₀ t) ∧
      filtrationExpectation G₀ = 0)
    (hneg₀ : filtrationExpectation
      (fun t ↦ (tensorFiltration F₀ G₀ t).map (tensorQuotientBaseChange q)) < 0) :
    ∃ (P : ℝ → Submodule K E) (R : ℝ → Submodule K V),
      (Antitone P ∧ (∃ t, P t = ⊥) ∧ (∃ t, P t = ⊤) ∧
        (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P s = P t) ∧
        filtrationExpectation P = 0) ∧
      (Antitone R ∧ (∃ t, R t = ⊥) ∧ (∃ t, R t = ⊤) ∧
        (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → R s = R t) ∧
        filtrationExpectation R = 0) ∧
      filtrationPairing P P + filtrationPairing R R = 1 ∧
      filtrationExpectation (fun t ↦ (tensorFiltration P R t).map q) < 0 := by
  let A := BinaryTensorFactors E V
  let e := binaryTensorEquiv K A
  let q' := q.comp e.toLinearMap
  have hprod : 0 < finrank K E * finrank K V := by
    rw [← Module.finrank_tensorProduct]
    exact hQ.trans_le (LinearMap.finrank_le_finrank_of_surjective hq)
  have ha : ∀ i, 0 < finrank K (A i) := by
    rintro (⟨⟩ | ⟨⟩)
    · exact Nat.pos_of_mul_pos_right hprod
    · exact Nat.pos_of_mul_pos_left hprod
  let F : ∀ i, ℝ → Submodule L (L ⊗[K] A i) := fun i ↦ match i with
    | .inl _ => F₀
    | .inr _ => G₀
  have hnegF : filtrationExpectation (fun t ↦
      (piTensorFiltration F t).map (piTensorQuotientBaseChange q')) < 0 := by
    exact (congrArg filtrationExpectation
      (funext (piTensor_image_binary_baseChange q F))).trans_lt hneg₀
  obtain ⟨P, hP, hPE, hnegP, hstable⟩ :=
    exists_galois_stable_normalized_negative_family q' (hq.comp e.surjective) ha F
      (by
        rintro (⟨⟩ | ⟨⟩)
        · exact hF₀
        · exact hG₀) hnegF
  let D : ∀ i, ℝ → Submodule K (A i) := fun i t ↦ rationalPart (P i t)
  have hD i := finite_filtration_rationalPart (P i) (hP i).1 (hP i).2.1
    (hP i).2.2.1 (hP i).2.2.2.1 (hstable i)
  have he i : (fun t ↦ (D i t).baseChange L) = P i := funext (hD i).1
  have hDc i : Antitone (D i) ∧ (∃ t, D i t = ⊥) ∧ (∃ t, D i t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → D i s = D i t) ∧
      filtrationExpectation (D i) = 0 := by
    refine ⟨(hD i).2.1, (hD i).2.2.1, (hD i).2.2.2.1, (hD i).2.2.2.2, ?_⟩
    rw [← filtrationExpectation_baseChange (L := L) (D i) (hD i).2.1
      (hD i).2.2.1 (hD i).2.2.2.1 (hD i).2.2.2.2, he]
    exact (hP i).2.2.2.2
  have hDe : (∑ i, filtrationPairing (D i) (D i)) = 1 := by
    calc
      _ = ∑ i, filtrationPairing (P i) (P i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← filtrationPairing_baseChange (L := L) (D i) (D i)
          (hD i).2.1 (hD i).2.2.1 (hD i).2.2.2.1 (hD i).2.2.2.2
          (hD i).2.1 (hD i).2.2.1 (hD i).2.2.2.1 (hD i).2.2.2.2, he]
      _ = 1 := hPE
  have hDn : filtrationExpectation (fun t ↦ (piTensorFiltration D t).map q') < 0 := by
    rw [← filtrationExpectation_piTensor_image_baseChange (L := L) D
      (fun i ↦ (hD i).2) q' (hq.comp e.surjective)]
    have he' : (fun i t ↦ (D i t).baseChange L) = P := funext he
    rw [he']
    exact hnegP
  refine ⟨D (.inl ()), D (.inr ()), hDc (.inl ()), hDc (.inr ()), ?_, ?_⟩
  · simpa only [Fintype.sum_sum_type, Fintype.sum_unique] using hDe
  · change filtrationExpectation (fun t ↦ (piTensorFiltration D t).map
      (q.comp (binaryTensorEquiv K A).toLinearMap)) < 0 at hDn
    simp_rw [map_comp, piTensorFiltration_map_binaryTensorEquiv] at hDn
    exact hDn

end BinaryRationality

end Submodule

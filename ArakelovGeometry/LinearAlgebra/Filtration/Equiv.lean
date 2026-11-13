/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.Pairing
public import ArakelovGeometry.LinearAlgebra.Filtration.Tensor

/-!
# Filtrations under linear equivalences

Transport preserves intrinsic expectations and pairings, including when the
source and target vector spaces belong to different universes.
-/

@[expose] public section

open Module
open scoped TensorProduct

namespace Submodule

variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]

/-- Strict right limits commute with the image of a linear map. -/
theorem filtrationRightLimit_map (f : E →ₗ[K] V) (F : ℝ → Submodule K E) (t : ℝ) :
    filtrationRightLimit (fun s ↦ (F s).map f) t = (filtrationRightLimit F t).map f := by
  simp only [filtrationRightLimit, map_iSup]

/-- Tensor filtrations commute with the image of both factor maps. -/
theorem tensorFiltration_map {E' V' : Type*} [AddCommGroup E'] [Module K E']
    [AddCommGroup V'] [Module K V'] (f : E →ₗ[K] E') (g : V →ₗ[K] V')
    (F : ℝ → Submodule K E) (G : ℝ → Submodule K V) (t : ℝ) :
    (tensorFiltration F G t).map (TensorProduct.map f g) =
      tensorFiltration (fun s ↦ (F s).map f) (fun s ↦ (G s).map g) t := by
  simp only [tensorFiltration, map_iSup, TensorProduct.range_mapIncl, map_map₂, map₂_map_map]
  apply iSup_congr
  intro a
  apply iSup_congr
  intro b
  apply iSup_congr
  intro h
  congr 1

variable [FiniteDimensional K E] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- Equivalence transport preserves the dimensions of actual filtration grades. -/
theorem finrank_filtrationGraded_map_equiv (e : E ≃ₗ[K] V)
    (F : ℝ → Submodule K E) (t : ℝ) :
    finrank K (FiltrationGraded (fun s ↦ (F s).map e.toLinearMap) t) =
      finrank K (FiltrationGraded F t) := by
  simp only [FiltrationGraded, finrank_quotient, finrank_comap_subtype]
  rw [filtrationRightLimit_map e.toLinearMap F t,
    ← map_inf e.toLinearMap e.injective, e.finrank_map_eq, e.finrank_map_eq]

omit [FiniteDimensional K V] in
/-- Equivalence transport preserves intrinsic expectation. -/
theorem filtrationExpectation_map_equiv (e : E ≃ₗ[K] V) (F : ℝ → Submodule K E) :
    filtrationExpectation (fun t ↦ (F t).map e.toLinearMap) = filtrationExpectation F := by
  simp only [filtrationExpectation, finrank_filtrationGraded_map_equiv, e.finrank_eq]

omit [FiniteDimensional K E] [FiniteDimensional K V] in
/-- Equivalence transport preserves the intrinsic pairing of two filtrations. -/
theorem filtrationPairing_map_equiv (e : E ≃ₗ[K] V) (F G : ℝ → Submodule K E) :
    filtrationPairing (fun t ↦ (F t).map e.toLinearMap)
      (fun t ↦ (G t).map e.toLinearMap) = filtrationPairing F G := by
  simp only [filtrationPairing, e.finrank_eq]
  congr 1
  apply finsum_congr
  intro p
  congr 2
  unfold filtrationJointMultiplicity
  rw [filtrationRightLimit_map e.toLinearMap F p.1,
    filtrationRightLimit_map e.toLinearMap G p.2,
    ← map_inf e.toLinearMap e.injective, ← map_inf e.toLinearMap e.injective,
    ← map_inf e.toLinearMap e.injective, ← map_sup, e.finrank_map_eq, e.finrank_map_eq]

omit [FiniteDimensional K V] in
/-- Equivalence transport preserves the finite, left-continuous centered condition. -/
theorem centered_filtration_map_equiv (e : E ≃ₗ[K] V) (F : ℝ → Submodule K E)
    (hF : Antitone F ∧ (∃ t, F t = ⊥) ∧ (∃ t, F t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) ∧
      filtrationExpectation F = 0) :
    Antitone (fun t ↦ (F t).map e.toLinearMap) ∧
      (∃ t, (F t).map e.toLinearMap = ⊥) ∧ (∃ t, (F t).map e.toLinearMap = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t →
        (F s).map e.toLinearMap = (F t).map e.toLinearMap) ∧
      filtrationExpectation (fun t ↦ (F t).map e.toLinearMap) = 0 := by
  refine ⟨fun _ _ h ↦ map_mono (hF.1 h), ?_, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hF.2.1
    exact ⟨t, by rw [ht, map_bot]⟩
  · obtain ⟨t, ht⟩ := hF.2.2.1
    exact ⟨t, by rw [ht, map_top]; exact LinearMap.range_eq_top.mpr e.surjective⟩
  · intro t
    obtain ⟨ε, hε, h⟩ := hF.2.2.2.1 t
    exact ⟨ε, hε, fun s hs ht ↦ congrArg (map e.toLinearMap) (h s hs ht)⟩
  · rw [filtrationExpectation_map_equiv, hF.2.2.2.2]

end Submodule

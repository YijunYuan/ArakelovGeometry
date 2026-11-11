/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Graded
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HNLift
public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Hermitian
public import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMap

/-!
# Finite images of actual Harder--Narasimhan filtrations

The image at a threshold is the sum of the images of the source thresholds.
The strict right limit commutes with this sum. All induced graded maps use
actual subquotient norms, as required in the componentwise proof of Bost's
Lemmas 7.1 and 7.2.
-/

@[expose] public section

open scoped TensorProduct BigOperators

namespace Submodule

variable {K ι Q : Type*} [Field K] [AddCommGroup Q] [Module K Q]
  {C : ι → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]

/-- The actual common image filtration of a family of filtered linear maps. -/
noncomputable def imageFiltration (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (t : ℝ) : Submodule K Q :=
  ⨆ i, (H i t).map (f i)

/-- Each source map preserves its filtration and the actual common image. -/
theorem le_comap_imageFiltration (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (i : ι) (t : ℝ) :
    H i t ≤ (imageFiltration f H t).comap (f i) :=
  map_le_iff_le_comap.mp (le_iSup (fun i ↦ (H i t).map (f i)) i)

/-- Taking strict right limits commutes with the common image, including the
empty family. This is an equality of actual subspaces. -/
theorem imageFiltration_rightLimit (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (t : ℝ) :
    filtrationRightLimit (imageFiltration f H) t =
      ⨆ i, (filtrationRightLimit (H i) t).map (f i) := by
  simp only [filtrationRightLimit, imageFiltration, map_iSup]
  exact iSup_comm

/-- The common image of decreasing filtrations is decreasing. -/
theorem imageFiltration_antitone (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (hH : ∀ i, Antitone (H i)) :
    Antitone (imageFiltration f H) := by
  intro s t hst
  exact iSup_mono fun i ↦ map_mono (hH i hst)

variable [Finite ι]

/-- Finitely many separated decreasing filtrations have a zero common image
above some threshold. -/
theorem imageFiltration_exists_bot (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (hH : ∀ i, Antitone (H i))
    (hbot : ∀ i, ∃ t, H i t = ⊥) : ∃ t, imageFiltration f H t = ⊥ := by
  classical
  choose t ht using hbot
  obtain ⟨b, hb⟩ := (Set.finite_range t).bddAbove
  refine ⟨b, bot_unique (iSup_le fun i ↦ ?_)⟩
  have hi : H i b = ⊥ := bot_unique ((hH i (hb ⟨i, rfl⟩)).trans_eq (ht i))
  simp only [hi, map_bot, le_refl]

/-- Finitely many exhaustive sources with spanning images give an exhaustive
common image filtration. -/
theorem imageFiltration_exists_top (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (hH : ∀ i, Antitone (H i))
    (htop : ∀ i, ∃ t, H i t = ⊤) (hspan : (⨆ i, (f i).range) = ⊤) :
    ∃ t, imageFiltration f H t = ⊤ := by
  classical
  choose t ht using htop
  obtain ⟨b, hb⟩ := (Set.finite_range t).bddBelow
  refine ⟨b, ?_⟩
  have hi (i : ι) : H i b = ⊤ := top_unique ((ht i).symm.le.trans (hH i (hb ⟨i, rfl⟩)))
  simpa only [imageFiltration, hi, map_top] using hspan

/-- Local constancy from the left passes to a finite common image. -/
theorem imageFiltration_left (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i))
    (hleft : ∀ i t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → H i s = H i t) (t : ℝ) :
    ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → imageFiltration f H s = imageFiltration f H t := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  by_cases hn : Nonempty ι
  · let : Nonempty ι := hn
    choose ε hε hc using fun i ↦ hleft i t
    let δ := Finset.univ.inf' Finset.univ_nonempty ε
    have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr (fun i _ ↦ hε i)
    refine ⟨δ, hδ, fun s hs hst ↦ ?_⟩
    apply iSup_congr
    intro i
    have hδε : δ ≤ ε i := Finset.inf'_le _ (Finset.mem_univ i)
    rw [hc i s (by linarith) hst]
  · have : IsEmpty ι := not_nonempty_iff.mp hn
    exact ⟨1, zero_lt_one, fun _ _ _ ↦ by simp [imageFiltration]⟩

/-- The canonical maps from the source grades jointly span the actual image
grade. No splitting of any source or target filtration is chosen. -/
theorem imageFiltration_graded_range (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (t : ℝ) :
    (⨆ i, (filtrationGradedMap (f i) (le_comap_imageFiltration f H i) t).range) = ⊤ := by
  let R := ⨆ i, (filtrationGradedMap (f i) (le_comap_imageFiltration f H i) t).range
  have hm (x : Q) (hx : x ∈ imageFiltration f H t) :
      filtrationGradedMk (imageFiltration f H) t ⟨x, hx⟩ ∈ R := by
    change x ∈ ⨆ i, (H i t).map (f i) at hx
    induction hx using iSup_induction' (fun i ↦ (H i t).map (f i)) with
    | mem i x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      apply (le_iSup (fun i ↦
        (filtrationGradedMap (f i) (le_comap_imageFiltration f H i) t).range) i)
      exact ⟨filtrationGradedMk (H i) t ⟨y, hy⟩, rfl⟩
    | zero => simpa using R.zero_mem
    | add x y hx hy ihx ihy =>
      change filtrationGradedMk (imageFiltration f H) t (⟨x, hx⟩ + ⟨y, hy⟩) ∈ R
      rw [map_add]
      exact R.add_mem ihx ihy
  apply top_unique
  intro z _
  obtain ⟨x, rfl⟩ := ((filtrationRightLimit (imageFiltration f H) t).comap
    (imageFiltration f H t).subtype).mkQ_surjective z
  exact hm x x.property

end Submodule

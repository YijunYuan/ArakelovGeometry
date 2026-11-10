/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.SlopesExtension

/-!
# Minimal slope along actual finite chains

The rational spaces may vary at every step. Tail maps are the actual
composites of the given maps, with identity at the last term. Testing a
nonzero quotient and choosing the first tail it detects gives a nonzero
map out of that step's actual cokernel. Zero cokernels are omitted from
the extended-real infimum, which is `⊤` for an empty index type.
-/

namespace ArakelovGeometry

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}

section LinearChain

variable {n : ℕ} (E : Fin (n + 1) → Type w)
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  (α : ∀ i : Fin n, E i.castSucc →ₗ[K] E i.succ)

/-- The actual composite from a chain term to its last term. -/
def linearChainTailMap (i : Fin (n + 1)) : E i →ₗ[K] E (Fin.last n) :=
  Fin.reverseInduction LinearMap.id (fun i β ↦ β.comp (α i)) i

/-- The last composite is the identity. -/
@[simp] theorem linearChainTailMap_last :
    linearChainTailMap E α (Fin.last n) = LinearMap.id :=
  Fin.reverseInduction_last

/-- The canonical composite commutes with each given chain map. -/
theorem linearChainTailMap_castSucc (i : Fin n) :
    linearChainTailMap E α i.castSucc = (linearChainTailMap E α i.succ).comp (α i) :=
  Fin.reverseInduction_castSucc i

/-- Injectivity of the source chain passes to its actual tail composites. -/
theorem linearChainTailMap_injective (hα : ∀ i, Function.Injective (α i))
    (i : Fin (n + 1)) : Function.Injective (linearChainTailMap E α i) := by
  induction i using Fin.reverseInduction with
  | last =>
    rw [linearChainTailMap_last]
    exact fun _ _ h ↦ h
  | cast i ih =>
    rw [linearChainTailMap_castSucc]
    exact ih.comp (hα i)

variable {G : Type w'} [AddCommGroup G] [Module K G]

/-- Every nonzero map out of a chain starting at zero detects a first
successor term, and vanishes on the preceding term's image. -/
theorem exists_first_nonzero_linearChainTailMap [Subsingleton (E 0)]
    (π : E (Fin.last n) →ₗ[K] G) (hπ : π ≠ 0) :
    ∃ i : Fin n, π.comp (linearChainTailMap E α i.succ) ≠ 0 ∧
      (π.comp (linearChainTailMap E α i.succ)).comp (α i) = 0 := by
  classical
  let t := Finset.univ.filter (fun i ↦ π.comp (linearChainTailMap E α i) ≠ 0)
  have hn : Fin.last n ∈ t := by
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and,
      linearChainTailMap_last, LinearMap.comp_id]
    exact hπ
  obtain ⟨j, hj, hleast⟩ := t.exists_min_image Fin.val ⟨Fin.last n, hn⟩
  have hjmap : π.comp (linearChainTailMap E α j) ≠ 0 := (Finset.mem_filter.mp hj).2
  have hj0 : j ≠ 0 := by
    intro hz
    subst j
    apply hjmap
    ext x
    rw [Subsingleton.elim x 0]
    simp only [map_zero]
  let i := j.pred hj0
  have hij : i.succ = j := Fin.succ_pred j hj0
  have hprev : π.comp (linearChainTailMap E α i.castSucc) = 0 := by
    by_contra hm
    have hi : i.castSucc ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
    have hmin := hleast i.castSucc hi
    change j.val ≤ i.val at hmin
    rw [← hij, Fin.val_succ] at hmin
    omega
  refine ⟨i, ?_, ?_⟩
  · rw [hij]
    exact hjmap
  · rwa [linearChainTailMap_castSucc, ← LinearMap.comp_assoc] at hprev

/-- The first detected chain term descends canonically to a nonzero map
out of its actual rational cokernel. -/
theorem exists_cokernel_map_of_linearChain [Subsingleton (E 0)]
    (π : E (Fin.last n) →ₗ[K] G) (hπ : π ≠ 0) :
    ∃ (i : Fin n) (g : (E i.succ ⧸ (α i).range) →ₗ[K] G), g ≠ 0 ∧
      g.comp (α i).range.mkQ = π.comp (linearChainTailMap E α i.succ) := by
  obtain ⟨i, hi, hz⟩ := exists_first_nonzero_linearChainTailMap E α π hπ
  let f : E i.succ →ₗ[K] G := π.comp (linearChainTailMap E α i.succ)
  have hk : (α i).range ≤ f.ker :=
    LinearMap.range_le_ker_iff.mpr hz
  let g : (E i.succ ⧸ (α i).range) →ₗ[K] G := (α i).range.liftQ f hk
  have hc : g.comp (α i).range.mkQ = f :=
    Submodule.liftQ_mkQ (α i).range f hk
  refine ⟨i, g, ?_, hc⟩
  intro hg
  rw [hg, LinearMap.zero_comp] at hc
  exact hi hc.symm

end LinearChain

namespace AdelicVectorBundle

section QuotientComparison

variable [S.IsProper] {E₁ : Type w} {E₂ : Type w'}
  [AddCommGroup E₁] [Module K E₁] [FiniteDimensional K E₁]
  [AddCommGroup E₂] [Module K E₂] [FiniteDimensional K E₂]
  (V₁ : AdelicVectorBundle S E₁) (V₂ : AdelicVectorBundle S E₂)

/-- A nonzero induced quotient map bounds the source quotient's minimal
slope using the height of the original map. -/
theorem minimalSlope_cokernel_sub_mapHeight_le_quotient_maximalSlope
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (U : Submodule K E₁) (T : Submodule K E₂) (f : E₁ →ₗ[K] E₂)
    (g : (E₁ ⧸ U) →ₗ[K] (E₂ ⧸ T)) (hg : g ≠ 0)
    (hc : g.comp U.mkQ = T.mkQ.comp f) :
    (V₁.quotientOfMeasurableBase U hS).minimalSlope hS hN - V₁.mapHeight V₂ f ≤
      (V₂.quotientOfMeasurableBase T hS).maximalSlope hS hN := by
  have hf : f ≠ 0 := by
    intro hz
    apply hg
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := U.mkQ_surjective y
    have hx := DFunLike.congr_fun hc x
    simpa only [hz, LinearMap.comp_zero, LinearMap.zero_apply, LinearMap.comp_apply] using hx
  have hh := V₁.mapHeight_quotient_le V₂ hS f hf U T g hg hc
  have hs := minimalSlope_sub_mapHeight_le_maximalSlope_of_ne_zero
    (V₁.quotientOfMeasurableBase U hS) (V₂.quotientOfMeasurableBase T hS) hS hN g hg
  exact (EReal.sub_le_sub le_rfl hh).trans hs

end QuotientComparison

variable [S.IsProper] {n : ℕ} (E : Fin (n + 1) → Type w)
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)] [∀ i, FiniteDimensional K (E i)]
  (V : ∀ i, AdelicVectorBundle S (E i))
  (α : ∀ i : Fin n, E i.castSucc →ₗ[K] E i.succ)

/-- Every nonzero actual quotient of the endpoint is bounded by a term
coming from a positive-rank actual cokernel in the chain. -/
theorem exists_cokernel_term_le_quotient_maximalSlope
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (h0 : Module.finrank K (E 0) = 0) (U : Submodule K (E (Fin.last n)))
    (hU : 0 < Module.finrank K (E (Fin.last n) ⧸ U)) :
    ∃ i : Fin n, 0 < Module.finrank K (E i.succ ⧸ (α i).range) ∧
      ((V i.succ).quotientOfMeasurableBase (α i).range hS).minimalSlope hS hN -
        (V i.succ).mapHeight (V (Fin.last n)) (linearChainTailMap E α i.succ) ≤
      ((V (Fin.last n)).quotientOfMeasurableBase U hS).maximalSlope hS hN := by
  classical
  let : Subsingleton (E 0) := Module.finrank_zero_iff.mp h0
  let : Nontrivial (E (Fin.last n) ⧸ U) := Module.nontrivial_of_finrank_pos hU
  have hπ : U.mkQ ≠ 0 := by
    intro hz
    obtain ⟨y, hy⟩ := exists_ne (0 : E (Fin.last n) ⧸ U)
    obtain ⟨x, hx⟩ := U.mkQ_surjective y
    exact hy (by simpa only [hz, LinearMap.zero_apply] using hx.symm)
  obtain ⟨i, g, hg, hc⟩ := exists_cokernel_map_of_linearChain E α U.mkQ hπ
  have hr : 0 < Module.finrank K g.range := Nat.pos_of_ne_zero (fun hz ↦
    hg (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
  refine ⟨i, hr.trans_le g.finrank_range_le, ?_⟩
  exact minimalSlope_cokernel_sub_mapHeight_le_quotient_maximalSlope
    (V i.succ) (V (Fin.last n)) hS hN (α i).range U
      (linearChainTailMap E α i.succ) g hg hc

/-- Source Proposition 4.3.33 for genuine finite chains of varying spaces
and given maps. In fact injectivity is unnecessary for this inequality.
Only nonzero actual cokernels contribute; an empty infimum is `⊤`.
All heights are those of the actual tail composites. -/
theorem minimalSlope_linearChain_lowerBound
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (h0 : Module.finrank K (E 0) = 0) :
    (⨅ i : {i : Fin n // 0 < Module.finrank K (E i.succ ⧸ (α i).range)},
      ((V i.val.succ).quotientOfMeasurableBase (α i.val).range hS).minimalSlope hS hN -
        (V i.val.succ).mapHeight (V (Fin.last n)) (linearChainTailMap E α i.val.succ)) ≤
      (V (Fin.last n)).minimalSlope hS hN := by
  apply (V (Fin.last n)).le_minimalSlope hS hN
  intro U hU
  obtain ⟨i, hi, hs⟩ :=
    exists_cokernel_term_le_quotient_maximalSlope E V α hS hN h0 U hU
  have hb :
      (⨅ j : {j : Fin n // 0 < Module.finrank K (E j.succ ⧸ (α j).range)},
        ((V j.val.succ).quotientOfMeasurableBase (α j.val).range hS).minimalSlope hS hN -
          (V j.val.succ).mapHeight (V (Fin.last n)) (linearChainTailMap E α j.val.succ)) ≤
      ((V i.succ).quotientOfMeasurableBase (α i).range hS).minimalSlope hS hN -
        (V i.succ).mapHeight (V (Fin.last n)) (linearChainTailMap E α i.succ) :=
    iInf_le (fun j : {j : Fin n // 0 < Module.finrank K (E j.succ ⧸ (α j).range)} ↦
      ((V j.val.succ).quotientOfMeasurableBase (α j.val).range hS).minimalSlope hS hN -
        (V j.val.succ).mapHeight (V (Fin.last n)) (linearChainTailMap E α j.val.succ)) ⟨i, hi⟩
  exact hb.trans hs

end AdelicVectorBundle

end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormalizedNumberFieldCurve

/-!
# The actual normalized number-field infinite locus and its total mass

The actual infinite places biject onto the Archimedean locus of the normalized
curve. Summing their produced singleton masses gives the number-field degree.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K] [NumberField K]

/-- The actual nontrivial class point of an infinite place. -/
def normalizedInfinitePlacePoint (w : NumberField.InfinitePlace K) :
    (normalizedNumberFieldAdelicStructure K).Ω :=
  ⟨Quotient.mk' w.val, mk_infinitePlace_ne_trivialPlace w⟩

/-- Different actual infinite places give different normalized class points. -/
theorem normalizedInfinitePlacePoint_injective :
    Function.Injective (normalizedInfinitePlacePoint (K := K)) := by
  intro w v h
  apply NumberField.InfinitePlace.eq_iff_isEquiv.mpr
  exact Quotient.eq'.mp (congrArg Subtype.val h)

/-- The actual infinite-place point belongs to the normalized curve's infinite locus. -/
theorem normalizedInfinitePlacePoint_mem_inf (w : NumberField.InfinitePlace K) :
    normalizedInfinitePlacePoint w ∈ (normalizedNumberFieldAdelicStructure K).Ωinf := by
  change ¬IsNonarchimedean (normalizedPlaceValue _)
  rw [show normalizedPlaceValue (normalizedInfinitePlacePoint w) = w.val from
    normalizedPlaceValue_eq_infinitePlace w]
  exact NumberField.infinitePlace_not_isNonarchimedean w

/-- All Archimedean points are exhausted by the actual infinite places. -/
theorem normalizedNumberFieldAdelicStructure_Ωinf_eq_range :
    (normalizedNumberFieldAdelicStructure K).Ωinf =
      Set.range (normalizedInfinitePlacePoint (K := K)) := by
  ext ω
  constructor
  · intro hω
    obtain ⟨w, hw⟩ := NumberField.exists_infinitePlace_of_not_isNonarchimedean hω
    refine ⟨w, Subtype.ext ?_⟩
    exact (Quotient.sound' hw).symm.trans (normalizedPlaceValue_class ω)
  · rintro ⟨w, rfl⟩
    exact normalizedInfinitePlacePoint_mem_inf w

/-- The produced actual infinite-place bijection onto the literal infinite locus. -/
def normalizedInfinitePlaceEquiv : NumberField.InfinitePlace K ≃
    (normalizedNumberFieldAdelicStructure K).Ωinf :=
  Equiv.ofBijective (fun w =>
    ⟨normalizedInfinitePlacePoint w, normalizedInfinitePlacePoint_mem_inf w⟩) (by
    constructor
    · intro w v h
      exact normalizedInfinitePlacePoint_injective (congrArg Subtype.val h)
    · intro ω
      obtain ⟨w, hw⟩ := normalizedNumberFieldAdelicStructure_Ωinf_eq_range.le ω.property
      exact ⟨w, Subtype.ext hw⟩)

/-- The actual infinite locus is finite via its produced infinite-place bijection. -/
instance normalizedInfiniteLocusFintype :
    Fintype (normalizedNumberFieldAdelicStructure K).Ωinf :=
  Fintype.ofEquiv (NumberField.InfinitePlace K) normalizedInfinitePlaceEquiv

/-- Finiteness of the literal set of normalized Archimedean points. -/
theorem normalizedNumberFieldAdelicStructure_Ωinf_finite :
    (normalizedNumberFieldAdelicStructure K).Ωinf.Finite := by
  rw [normalizedNumberFieldAdelicStructure_Ωinf_eq_range]
  exact Set.finite_range _

/-- The literal sum of actual infinite-place singleton masses is the number-field degree. -/
theorem normalizedNumberFieldAdelicStructure_sum_infinitePlace_mass :
    (∑ w : NumberField.InfinitePlace K,
      (normalizedNumberFieldAdelicStructure K).v {normalizedInfinitePlacePoint w}) =
        (Module.finrank ℚ K : ENNReal) := by
  calc
    _ = ∑ w : NumberField.InfinitePlace K, (w.mult : ENNReal) := by
      apply Finset.sum_congr rfl
      intro w _
      exact normalizedNumberFieldAdelicStructure_v_infinitePlace w
    _ = _ := by exact_mod_cast (NumberField.InfinitePlace.sum_mult_eq (K := K))

/-- The literal singleton sum over the actual infinite locus is the number-field degree. -/
theorem normalizedNumberFieldAdelicStructure_sum_infinite_mass :
    (∑ ω : (normalizedNumberFieldAdelicStructure K).Ωinf,
      (normalizedNumberFieldAdelicStructure K).v {ω.val}) =
        (Module.finrank ℚ K : ENNReal) := by
  rw [← normalizedInfinitePlaceEquiv.sum_comp
    (fun ω => (normalizedNumberFieldAdelicStructure K).v {ω.val})]
  exact normalizedNumberFieldAdelicStructure_sum_infinitePlace_mass

/-- The actual infinite-locus measure is its finite singleton sum. -/
theorem normalizedNumberFieldAdelicStructure_v_Ωinf_eq_sum :
    (normalizedNumberFieldAdelicStructure K).v (normalizedNumberFieldAdelicStructure K).Ωinf =
      ∑ ω : (normalizedNumberFieldAdelicStructure K).Ωinf,
        (normalizedNumberFieldAdelicStructure K).v {ω.val} := by
  classical
  have : MeasurableSingletonClass (normalizedNumberFieldAdelicStructure K).Ω := by
    change MeasurableSingletonClass
      {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}
    infer_instance
  let s : Finset (normalizedNumberFieldAdelicStructure K).Ω :=
    Finset.univ.image (fun ω : (normalizedNumberFieldAdelicStructure K).Ωinf => ω.val)
  have hs : (s : Set (normalizedNumberFieldAdelicStructure K).Ω) =
      (normalizedNumberFieldAdelicStructure K).Ωinf := by
    ext ω
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range, SetCoe.exists, exists_prop, exists_eq_right]
  calc
    _ = (normalizedNumberFieldAdelicStructure K).v s := congrArg _ hs.symm
    _ = ∑ ω ∈ s, (normalizedNumberFieldAdelicStructure K).v {ω} :=
      sum_measure_singleton.symm
    _ = _ := Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)

/-- The actual normalized curve has total infinite mass equal to its rational degree. -/
theorem normalizedNumberFieldAdelicStructure_v_Ωinf :
    (normalizedNumberFieldAdelicStructure K).v (normalizedNumberFieldAdelicStructure K).Ωinf =
      (Module.finrank ℚ K : ENNReal) := by
  rw [normalizedNumberFieldAdelicStructure_v_Ωinf_eq_sum,
    normalizedNumberFieldAdelicStructure_sum_infinite_mass]

end ArakelovGeometry.AdelicStructure

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.GeometryOfNumbers.LatticeSpanningBody
import ArakelovGeometry.GeometryOfNumbers.LatticeDualCentralSection
import ArakelovGeometry.GeometryOfNumbers.PrimitiveLatticeFiberBound
import ArakelovGeometry.GeometryOfNumbers.PrimitiveLineDualMeasure

/-! # Actual spanning-polar lattice counting -/

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.LatticeSpanningPolarCount

open Module MeasureTheory Set
open LatticeSubspaceBasis LatticeSubspaceCoordinates LatticePrimitiveVector

section DimensionZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Subsingleton E] [MeasurableSpace E] [BorelSpace E]

/-- In actual dimension zero every lattice-normalized Haar measure has total mass one. -/
theorem normalizedMeasure_univ_of_subsingleton (L : Submodule ℤ E)
    (μ : Measure E) [μ.IsAddHaarMeasure] : latticeNormalizedMeasure L μ univ = 1 := by
  let b := Module.finBasis ℝ E
  have hL : Submodule.span ℤ (Set.range b) = L := Subsingleton.elim _ _
  have hp : parallelepiped b = (univ : Set E) := by
    ext x
    rw [parallelepiped_basis_eq]
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    intro i
    simp [Subsingleton.elim x 0]
  rw [← hL, latticeNormalizedMeasure_span_basis, ← hp]
  exact b.addHaar_self

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The actual original body lattice-point subtype has one element in dimension zero. -/
theorem card_body_of_subsingleton (L : Submodule ℤ E) {C : Set E} (h0 : (0 : E) ∈ C) :
    Nat.card {x : L // (x : E) ∈ C} = 1 := by
  let : Unique {x : L // (x : E) ∈ C} := uniqueOfSubsingleton ⟨0, by simpa using h0⟩
  exact Nat.card_unique

omit [MeasurableSpace E] [BorelSpace E] in
/-- The actual polar-volume/count product is exactly one in the zero-dimensional base case. -/
theorem card_mul_normalizedMeasure_polar_of_subsingleton
    (L : Submodule ℤ E) [MeasurableSpace (StrongDual ℝ E)] [BorelSpace (StrongDual ℝ E)]
    (μ : Measure (StrongDual ℝ E)) [μ.IsAddHaarMeasure]
    {C : Set E} (h0 : (0 : E) ∈ C) :
    (Nat.card {x : L // (x : E) ∈ C} : ℝ) *
      (latticeNormalizedMeasure (integralDual L) μ (StrongDual.polar ℝ C)).toReal = 1 := by
  have hp : StrongDual.polar ℝ C = (univ : Set (StrongDual ℝ E)) := by
    ext f
    simp only [StrongDual.mem_polar_iff, mem_univ, iff_true]
    intro x _
    simp [Subsingleton.elim x 0]
  rw [card_body_of_subsingleton L h0, hp, normalizedMeasure_univ_of_subsingleton]
  norm_num

end DimensionZero

section Spanning

open LatticeSpanningBody PrimitiveAffineSections PrimitiveLineMeasure PrimitiveLineDualMeasure
open LatticeDualCentralSection PrimitiveLatticeFiberBound LatticeSubspaceQuotient LatticeFiberCount

attribute [local instance] Submodule.closed_of_finiteDimensional

/-- The original lattice-point count times the actual integral-dual normalized polar volume
is at most `6 ^ dim E` when the original body lattice points span. -/
theorem card_mul_normalizedMeasure_polar_le_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    [MeasurableSpace (StrongDual ℝ E)] [BorelSpace (StrongDual ℝ E)]
    (μ : Measure (StrongDual ℝ E)) [μ.IsAddHaarMeasure]
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (h0 : (0 : E) ∈ C)
    (hspan : Submodule.span ℝ (C ∩ (L : Set E)) = ⊤) :
    (Nat.card {x : L // (x : E) ∈ C} : ℝ) *
      (latticeNormalizedMeasure (integralDual L) μ (StrongDual.polar ℝ C)).toReal ≤
        6 ^ Module.finrank ℝ E := by
  generalize hn : Module.finrank ℝ E = n
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    by_cases hn0 : n = 0
    · let := Module.finrank_zero_iff.mp (hn.trans hn0)
      rw [card_mul_normalizedMeasure_polar_of_subsingleton L μ h0, hn0]
      norm_num
    · have hdpos : 0 < Module.finrank ℝ E := by omega
      have : Nontrivial E := Module.nontrivial_of_finrank_pos hdpos
      obtain ⟨x, hxC, hxL, hx⟩ := exists_nonzero_latticePoint_of_span L hspan
      obtain ⟨v, hv, hvC, hprimitive, _⟩ :=
        exists_primitive_mem L hconvex hsymm ⟨x, ⟨hxC, hxL⟩, hx⟩
      let U : Submodule ℝ E := ℝ ∙ (v : E)
      have hU : Submodule.span ℝ ((L ⊓ U.restrictScalars ℤ : Submodule ℤ E) : Set E) = U :=
        span_singleton_rational L v.property
      let := quotientImage_discrete L U hU
      let := quotientImage_isZLattice L U hU
      let := intersectionAsSubmodule_discrete L U hU
      let := intersectionAsSubmodule_isZLattice L U hU
      let := integralDual_discrete (quotientImage L U)
      let := integralDual_isZLattice (quotientImage L U)
      let := integralDual_discrete (intersectionAsSubmodule L U)
      let := integralDual_isZLattice (intersectionAsSubmodule L U)
      let : MeasurableSpace (E ⧸ U) := borel _
      let : BorelSpace (E ⧸ U) := ⟨rfl⟩
      let : MeasurableSpace (StrongDual ℝ (E ⧸ U)) := borel _
      let : BorelSpace (StrongDual ℝ (E ⧸ U)) := ⟨rfl⟩
      let : MeasurableSpace (StrongDual ℝ U) := borel _
      let : BorelSpace (StrongDual ℝ U) := ⟨rfl⟩
      let η := (Module.finBasis ℝ U).addHaar
      let ν := (Module.finBasis ℝ (StrongDual ℝ (E ⧸ U))).addHaar
      let ξ := (Module.finBasis ℝ (StrongDual ℝ U)).addHaar
      let := latticeNormalizedMeasure_isAddHaar (integralDual (quotientImage L U)) ν
      let := latticeNormalizedMeasure_isAddHaar (integralDual (intersectionAsSubmodule L U)) ξ
      have hqcompact : IsCompact (U.mkQ '' C) :=
        hcompact.image U.mkQ.continuous_of_finiteDimensional
      have hqconvex : Convex ℝ (U.mkQ '' C) := hconvex.linear_image U.mkQ
      have hqsymm : ∀ y ∈ U.mkQ '' C, -y ∈ U.mkQ '' C := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨-y, hsymm y hy, map_neg _ _⟩
      have hq0 : (0 : E ⧸ U) ∈ U.mkQ '' C := ⟨0, h0, map_zero _⟩
      have hqspan := quotient_latticePoints_span L U hspan
      have hqdim : Module.finrank ℝ (E ⧸ U) < n := by
        have hd := finrank_quotient_line_add_one hv
        change Module.finrank ℝ (E ⧸ U) + 1 = Module.finrank ℝ E at hd
        omega
      have hIH := ih _ hqdim (E := E ⧸ U) (quotientImage L U) ν
        hqcompact hqconvex hqsymm hq0 hqspan rfl
      have hcount := card_body_le_three_halves_section_mul_quotient L v hv η hprimitive
        hcompact hconvex hsymm hvC
      have hzero := zero_mem_interior_of_lattice_span L hconvex hsymm h0 hspan
      have hpolar := normalizedMeasure_polar_le_quotient_mul_intersection L U hU μ ν ξ
        hcompact hconvex hsymm hzero
      have hfactor := normalizedMeasure_primitiveLine_polar_toReal_eq_four_div L v hv η ξ
        hprimitive hcompact hconvex hsymm hvC
      have hlength := two_le_volume_central hcompact hconvex hsymm hv hvC
      simp only [affineSection, add_zero] at hlength
      rw [← latticeNormalizedMeasure_section_eq_volume_preimage L v hv η hprimitive
        hcompact.isClosed.measurableSet] at hlength
      have hqzero := zero_mem_interior_of_lattice_span (quotientImage L U)
        hqconvex hqsymm hq0 hqspan
      have hjnhds : U.subtype ⁻¹' C ∈ nhds (0 : U) :=
        continuous_subtype_val.continuousAt.preimage_mem_nhds
          (mem_interior_iff_mem_nhds.mp hzero)
      have hqfinite := (polar_isCompact (mem_interior_iff_mem_nhds.mp hqzero)).measure_lt_top
        (μ := latticeNormalizedMeasure (integralDual (quotientImage L U)) ν)
      have hjfinite := (polar_isCompact hjnhds).measure_lt_top
        (μ := latticeNormalizedMeasure (integralDual (intersectionAsSubmodule L U)) ξ)
      have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hqfinite.ne hjfinite.ne) hpolar
      rw [ENNReal.toReal_mul, hfactor] at hreal
      calc
        _ ≤ (((3 / 2 : ℝ) * (latticeNormalizedMeasure (intersectionAsSubmodule L U) η
              (U.subtype ⁻¹' C)).toReal) * Nat.card (quotientPoints L U C)) *
            ((latticeNormalizedMeasure (integralDual (quotientImage L U)) ν
              (StrongDual.polar ℝ (U.mkQ '' C))).toReal *
              (4 / (latticeNormalizedMeasure (intersectionAsSubmodule L U) η
                (U.subtype ⁻¹' C)).toReal)) :=
          mul_le_mul hcount hreal ENNReal.toReal_nonneg (by positivity)
        _ = 6 * ((Nat.card (quotientPoints L U C) : ℝ) *
            (latticeNormalizedMeasure (integralDual (quotientImage L U)) ν
              (StrongDual.polar ℝ (U.mkQ '' C))).toReal) := by
          have hne : (latticeNormalizedMeasure (intersectionAsSubmodule L U) η
              (U.subtype ⁻¹' C)).toReal ≠ 0 := by linarith
          field_simp
          ring
        _ ≤ 6 * 6 ^ Module.finrank ℝ (E ⧸ U) := mul_le_mul_of_nonneg_left hIH (by norm_num)
        _ = 6 ^ n := by
          rw [mul_comm, ← pow_succ]
          congr 1
          have hd := finrank_quotient_line_add_one hv
          change Module.finrank ℝ (E ⧸ U) + 1 = Module.finrank ℝ E at hd
          omega

end Spanning

end ArakelovGeometry.GeometryOfNumbers.LatticeSpanningPolarCount

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.GeometryOfNumbers.LatticePolarSpan

/-! # The sharp lower lattice-count estimate

The closed central section along the annihilator of the polar lattice span gives
the Gillet–Soulé lower estimate, with the constant `6 ^ finrank ℝ E`.
-/

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.LatticePolarCountLower

open Set MeasureTheory
open LatticeSubspaceCoordinates LatticeSubspaceQuotient LatticeSubspaceBasis
open LatticeIntegralDualCoordinates LatticePolarSpan
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Inclusion sends the literal intersection-section lattice points into the original
body's lattice points, independently of rationality of the subspace. -/
def sectionLatticePointsInclusion (L : Submodule ℤ E) (W : Submodule ℝ E) (C : Set E) :
    {x : intersectionAsSubmodule L W // (x : W) ∈ W.subtype ⁻¹' C} →
      {x : L // (x : E) ∈ C} :=
  fun x => ⟨⟨((x.val : W) : E), x.val.property⟩, x.property⟩

/-- The actual section-point inclusion is injective. -/
theorem sectionLatticePointsInclusion_injective
    (L : Submodule ℤ E) (W : Submodule ℝ E) (C : Set E) :
    Function.Injective (sectionLatticePointsInclusion L W C) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z => ((z.val : L) : E)) h

attribute [local instance] Submodule.closed_of_finiteDimensional

variable [FiniteDimensional ℝ E]

/-- Closed-section lattice counts are bounded by the original compact-body lattice count. -/
theorem card_section_le (L : Submodule ℤ E) [DiscreteTopology L]
    (W : Submodule ℝ E) {C : Set E} (hcompact : IsCompact C) :
    Nat.card {x : intersectionAsSubmodule L W // (x : W) ∈ W.subtype ⁻¹' C} ≤
      Nat.card {x : L // (x : E) ∈ C} := by
  let : Finite {x : L // (x : E) ∈ C} :=
    (LatticeCount.finite_subgroup_points_of_bounded L.toAddSubgroup
      hcompact.isBounded).to_subtype
  exact Nat.card_le_card_of_injective (sectionLatticePointsInclusion L W C)
    (sectionLatticePointsInclusion_injective L W C)

/-- Averaging on the closed rational section and the actual inclusion control its
normalized volume by the original body's lattice count. -/
theorem normalizedMeasure_section_le_two_pow_card
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (W : Submodule ℝ E)
    (hW : Submodule.span ℝ ((L : Set E) ∩ (W : Set E)) = W)
    [MeasurableSpace W] [BorelSpace W]
    (ν : Measure W) [ν.IsAddHaarMeasure]
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) :
    (latticeNormalizedMeasure (intersectionAsSubmodule L W) ν (W.subtype ⁻¹' C)).toReal ≤
      2 ^ Module.finrank ℝ W * (Nat.card {x : L // (x : E) ∈ C} : ℝ) := by
  let := intersectionAsSubmodule_discrete L W hW
  let := intersectionAsSubmodule_isZLattice L W hW
  have hc : IsCompact (W.subtype ⁻¹' C) :=
    (W.isClosedEmbedding_subtype W.closed_of_finiteDimensional).isCompact_preimage hcompact
  have hs : ∀ w ∈ W.subtype ⁻¹' C, -w ∈ W.subtype ⁻¹' C :=
    fun w hw => hsymm w hw
  have h := latticeNormalizedMeasure_le_two_pow_card (intersectionAsSubmodule L W) ν
    hc.isClosed.measurableSet hc.isBounded (hconvex.linear_preimage W.subtype) hs
  have hr := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast] at hr
  exact hr.trans (mul_le_mul_of_nonneg_left
    (by exact_mod_cast card_section_le L W hcompact) (by positivity))

variable [MeasurableSpace E] [BorelSpace E]

/-- The actual normalized body volume times the actual polar lattice count is bounded
by `6 ^ dim E` times the actual body lattice count. All hypotheses are geometric. -/
theorem normalizedMeasure_mul_card_polar_le_pow_mul_card
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    (latticeNormalizedMeasure L μ C).toReal *
      (Nat.card {f : integralDual L // (f : StrongDual ℝ E) ∈ StrongDual.polar ℝ C} : ℝ) ≤
      6 ^ Module.finrank ℝ E * (Nat.card {x : L // (x : E) ∈ C} : ℝ) := by
  let U := polarLatticeSpan L C
  let W := annihilator U
  have hU := polarLatticeSpan_rational L C
  have hW := annihilator_rational L U hU
  let : MeasurableSpace W := borel _
  let : BorelSpace W := ⟨rfl⟩
  let : MeasurableSpace (E ⧸ W) := borel _
  let : BorelSpace (E ⧸ W) := ⟨rfl⟩
  let ν := (Module.finBasis ℝ W).addHaar
  let ξ := (Module.finBasis ℝ (E ⧸ W)).addHaar
  let := intersectionAsSubmodule_discrete L W hW
  let := intersectionAsSubmodule_isZLattice L W hW
  let := quotientImage_discrete L W hW
  let := quotientImage_isZLattice L W hW
  let := latticeNormalizedMeasure_isAddHaar (intersectionAsSubmodule L W) ν
  let := latticeNormalizedMeasure_isAddHaar (quotientImage L W) ξ
  have hcS : IsCompact (W.subtype ⁻¹' C) :=
    (W.isClosedEmbedding_subtype W.closed_of_finiteDimensional).isCompact_preimage hcompact
  have hcQ : IsCompact (W.mkQ '' C) :=
    hcompact.image W.mkQ.continuous_of_finiteDimensional
  have hsplit := LatticeCentralSection.latticeNormalizedMeasure_le_intersection_mul_quotient
    L W hW μ ν ξ hcompact hconvex hsymm
  have hsplitR := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hcS.measure_lt_top.ne hcQ.measure_lt_top.ne) hsplit
  rw [ENNReal.toReal_mul] at hsplitR
  have hsec := normalizedMeasure_section_le_two_pow_card L W hW ν hcompact hconvex hsymm
  have hpolar := card_polar_mul_normalizedMeasure_quotient_le_pow
    L C ξ hcompact hconvex hsymm hzero
  have hdimQ : Module.finrank ℝ (E ⧸ W) = Module.finrank ℝ U := by
    rw [(quotientEvaluation L U hU).toLinearEquiv.finrank_eq]
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := U) (F' := ℝ)).finrank_eq]
    exact Subspace.dual_finrank_eq
  have hdim : Module.finrank ℝ W + Module.finrank ℝ U = Module.finrank ℝ E := by
    rw [← hdimQ, Nat.add_comm]
    exact Submodule.finrank_quotient_add_finrank W
  calc
    _ ≤ ((latticeNormalizedMeasure (intersectionAsSubmodule L W) ν
          (W.subtype ⁻¹' C)).toReal *
          (latticeNormalizedMeasure (quotientImage L W) ξ (W.mkQ '' C)).toReal) *
        (Nat.card {f : integralDual L // (f : StrongDual ℝ E) ∈ StrongDual.polar ℝ C} : ℝ) :=
      mul_le_mul_of_nonneg_right hsplitR (by positivity)
    _ ≤ (2 ^ Module.finrank ℝ W * (Nat.card {x : L // (x : E) ∈ C} : ℝ)) *
        ((Nat.card {f : integralDual L // (f : StrongDual ℝ E) ∈ StrongDual.polar ℝ C} : ℝ) *
          (latticeNormalizedMeasure (quotientImage L W) ξ (W.mkQ '' C)).toReal) := by
      rw [mul_assoc, mul_comm _ (Nat.card _ : ℝ)]
      exact mul_le_mul_of_nonneg_right hsec (by positivity)
    _ ≤ (2 ^ Module.finrank ℝ W * (Nat.card {x : L // (x : E) ∈ C} : ℝ)) *
        6 ^ Module.finrank ℝ U :=
      mul_le_mul_of_nonneg_left hpolar (by positivity)
    _ ≤ (6 : ℝ) ^ Module.finrank ℝ W * 6 ^ Module.finrank ℝ U *
        (Nat.card {x : L // (x : E) ∈ C} : ℝ) := by
      have hp : (2 : ℝ) ^ Module.finrank ℝ W ≤ 6 ^ Module.finrank ℝ W := by
        gcongr
        norm_num
      nlinarith [mul_nonneg
        (mul_nonneg (sub_nonneg.mpr hp) (Nat.cast_nonneg (Nat.card {x : L // (x : E) ∈ C})))
        (show (0 : ℝ) ≤ 6 ^ Module.finrank ℝ U by positivity)]
    _ = _ := by rw [← pow_add, hdim]

/-- The equivalent lower-count form of the sharp polar lattice estimate. -/
theorem pow_inv_mul_normalizedMeasure_mul_card_polar_le_card
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    ((6 : ℝ) ^ Module.finrank ℝ E)⁻¹ *
      (latticeNormalizedMeasure L μ C).toReal *
      (Nat.card {f : integralDual L // (f : StrongDual ℝ E) ∈ StrongDual.polar ℝ C} : ℝ) ≤
      (Nat.card {x : L // (x : E) ∈ C} : ℝ) := by
  have h := normalizedMeasure_mul_card_polar_le_pow_mul_card L μ hcompact hconvex hsymm hzero
  have hp : (0 : ℝ) < 6 ^ Module.finrank ℝ E := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le), inv_mul_cancel₀ hp.ne']

omit [MeasurableSpace E] [BorelSpace E] in
/-- Canonical evaluation identifies original body lattice points with actual bipolar
double-integral-dual lattice points. -/
theorem card_bipolar_eq_card
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ C) :
    Nat.card {g : integralDual (integralDual L) //
      (g : StrongDual ℝ (StrongDual ℝ E)) ∈ StrongDual.polar ℝ (StrongDual.polar ℝ C)} =
      Nat.card {x : L // (x : E) ∈ C} := by
  let e := doubleDualEquiv (E := E)
  have heL := doubleDualEquiv_comap_integralDual L
  have heC := doubleDualEquiv_image_eq_bipolar hcompact.isClosed hconvex hsymm hzero
  let f : {x : L // (x : E) ∈ C} →
      {g : integralDual (integralDual L) //
        (g : StrongDual ℝ (StrongDual ℝ E)) ∈ StrongDual.polar ℝ (StrongDual.polar ℝ C)} :=
    fun x => ⟨⟨e x.val, by
      have hx : (x.val : E) ∈ ZLattice.comap ℝ (integralDual (integralDual L))
          e.toLinearMap := by rw [heL]; exact x.val.property
      exact hx⟩, heC ▸ Set.mem_image_of_mem e x.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact e.injective (congrArg (fun g => ((g.val : integralDual (integralDual L)) :
        StrongDual ℝ (StrongDual ℝ E))) h)
    · intro g
      have hg := g.property
      simp only [← heC] at hg
      obtain ⟨x, hx, hxg⟩ := hg
      have hxL : x ∈ L := by
        rw [← heL]
        change e x ∈ integralDual (integralDual L)
        rw [hxg]
        exact g.val.property
      exact ⟨⟨⟨x, hxL⟩, hx⟩, Subtype.ext (Subtype.ext hxg)⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

omit [MeasurableSpace E] [BorelSpace E] in
/-- Applying the sharp estimate to the literal polar and actual integral dual gives
the dual-body inequality used in arithmetic section comparison. -/
theorem normalizedMeasure_polar_mul_card_le_pow_mul_card_polar
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    [MeasurableSpace (StrongDual ℝ E)] [BorelSpace (StrongDual ℝ E)]
    (μ : Measure (StrongDual ℝ E)) [μ.IsAddHaarMeasure]
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    (latticeNormalizedMeasure (integralDual L) μ (StrongDual.polar ℝ C)).toReal *
      (Nat.card {x : L // (x : E) ∈ C} : ℝ) ≤
      6 ^ Module.finrank ℝ E *
        (Nat.card {f : integralDual L // (f : StrongDual ℝ E) ∈ StrongDual.polar ℝ C} : ℝ) := by
  let := integralDual_discrete L
  let := integralDual_isZLattice L
  obtain ⟨hc, hv, hs, hz, _⟩ := polar_body_properties hcompact hconvex hsymm hzero
  have h := normalizedMeasure_mul_card_polar_le_pow_mul_card
    (integralDual L) μ hc hv hs hz
  rw [card_bipolar_eq_card L hcompact hconvex hsymm (interior_subset hzero)] at h
  have hd : Module.finrank ℝ (StrongDual ℝ E) = Module.finrank ℝ E := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finrank_eq]
    exact Subspace.dual_finrank_eq
  simpa only [hd] using h

end ArakelovGeometry.GeometryOfNumbers.LatticePolarCountLower

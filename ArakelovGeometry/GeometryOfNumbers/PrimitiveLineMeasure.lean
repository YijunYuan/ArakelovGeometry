/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.LatticePrimitiveVector
public import ArakelovGeometry.GeometryOfNumbers.LatticeSubspaceCoordinates
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Actual primitive-line coordinates and their normalized Haar measure -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.PrimitiveLineMeasure

open MeasureTheory Set LatticeSubspaceCoordinates LatticePrimitiveVector

/-- The actual unit integer submodule has the discrete real-subspace topology. -/
theorem integerLattice_discrete : DiscreteTopology (ℤ ∙ (1 : ℝ)) := by
  change DiscreteTopology (ℤ ∙ (1 : ℝ) : Submodule ℤ ℝ).toAddSubgroup
  rw [Submodule.span_singleton_toAddSubgroup_eq_zmultiples]
  infer_instance

/-- The real span of the actual integer lattice is the whole real line. -/
theorem integerLattice_isZLattice :
    letI := integerLattice_discrete
    IsZLattice ℝ (ℤ ∙ (1 : ℝ)) := by
  let := integerLattice_discrete
  constructor
  apply eq_top_iff.mpr
  intro x _
  have h1 : (1 : ℝ) ∈ Submodule.span ℝ ((ℤ ∙ (1 : ℝ) : Submodule ℤ ℝ) : Set ℝ) :=
    Submodule.subset_span (Submodule.mem_span_singleton_self _)
  simpa only [smul_eq_mul, mul_one] using
    (Submodule.span ℝ ((ℤ ∙ (1 : ℝ) : Submodule ℤ ℝ) : Set ℝ)).smul_mem x h1

/-- Normalization by the actual unit integer lattice gives ordinary Lebesgue measure. -/
theorem integerLattice_normalizedMeasure_eq_volume (μ : Measure ℝ) [μ.IsAddHaarMeasure] :
    letI := integerLattice_discrete
    letI := integerLattice_isZLattice
    latticeNormalizedMeasure (ℤ ∙ (1 : ℝ)) μ = volume := by
  let := integerLattice_discrete
  let := integerLattice_isZLattice
  apply latticeNormalizedMeasure_eq_of_domain_measure_one
    (ℤ ∙ (1 : ℝ)) μ volume (F := Ioc 0 1)
  · refine IsAddFundamentalDomain.mk' nullMeasurableSet_Ioc fun x => ?_
    let f : ℤ → (ℤ ∙ (1 : ℝ) : Submodule ℤ ℝ) := fun n =>
      ⟨n • (1 : ℝ), Submodule.mem_span_singleton.mpr ⟨n, rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro m n h
        have hr : (m : ℝ) = (n : ℝ) := by simpa [f] using congrArg Subtype.val h
        exact_mod_cast hr
      · rintro ⟨t, ht⟩
        obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp ht
        exact ⟨n, Subtype.ext hn⟩
    apply hf.existsUnique_iff.mpr
    change ∃! n : ℤ, n • (1 : ℝ) + x ∈ Ioc 0 1
    simpa [f, add_comm] using existsUnique_add_zsmul_mem_Ioc zero_lt_one x (0 : ℝ)
  · simp

section ActualLine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (v : L) (hv : (v : E) ≠ 0)

attribute [local instance] Submodule.closed_of_finiteDimensional

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- The actual integer pullback of the primitive line is exactly the unit integer lattice. -/
theorem comap_intersection_toSpanNonzeroSingleton
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E)) :
    ZLattice.comap ℝ (intersectionAsSubmodule L (ℝ ∙ (v : E)))
      (ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ (v : E) hv).toLinearMap =
        ℤ ∙ (1 : ℝ) := by
  ext t
  change t • (v : E) ∈ L ↔ t ∈ ℤ ∙ (1 : ℝ)
  constructor
  · intro ht
    have hin : t • (v : E) ∈ L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ :=
      ⟨ht, (ℝ ∙ (v : E)).smul_mem t (Submodule.mem_span_singleton_self _)⟩
    rw [hprimitive] at hin
    obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hin
    have hnt : (n : ℝ) = t := smul_left_injective ℝ hv
      (by simpa only [Int.cast_smul_eq_zsmul] using hn)
    exact Submodule.mem_span_singleton.mpr ⟨n, by simpa using hnt⟩
  · intro ht
    obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp ht
    have htn : t = (n : ℝ) := by simpa using hn.symm
    rw [htn, Int.cast_smul_eq_zsmul]
    exact L.smul_mem n v.property

section Measure

variable [MeasurableSpace (ℝ ∙ (v : E))] [BorelSpace (ℝ ∙ (v : E))]
  (ν : Measure (ℝ ∙ (v : E))) [ν.IsAddHaarMeasure]

/-- The primitive coordinate preserves ordinary Lebesgue and actual intersection-normalized Haar. -/
theorem measurePreserving_toSpanNonzeroSingleton
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E)) :
    MeasurePreserving (ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ (v : E) hv)
      volume (latticeNormalizedMeasure (intersectionAsSubmodule L (ℝ ∙ (v : E))) ν) := by
  let hU := span_singleton_rational L v.property
  let := intersectionAsSubmodule_discrete L (ℝ ∙ (v : E)) hU
  let := intersectionAsSubmodule_isZLattice L (ℝ ∙ (v : E)) hU
  let := integerLattice_discrete
  let := integerLattice_isZLattice
  have h := measurePreserving_latticeNormalizedMeasure_comap
    (intersectionAsSubmodule L (ℝ ∙ (v : E)))
    (ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ (v : E) hv) ν volume
  rw [comap_intersection_toSpanNonzeroSingleton L v hv hprimitive,
    integerLattice_normalizedMeasure_eq_volume] at h
  exact h

include hv in
/-- The actual line-normalized section volume equals its literal real-coordinate length. -/
theorem latticeNormalizedMeasure_section_eq_volume_preimage
    (hprimitive : L ⊓ (ℝ ∙ (v : E)).restrictScalars ℤ = ℤ ∙ (v : E))
    [MeasurableSpace E] [BorelSpace E] {C : Set E} (hC : MeasurableSet C) :
    latticeNormalizedMeasure (intersectionAsSubmodule L (ℝ ∙ (v : E))) ν
        ((ℝ ∙ (v : E)).subtype ⁻¹' C) =
      volume ((fun t : ℝ => t • (v : E)) ⁻¹' C) := by
  have h := (measurePreserving_toSpanNonzeroSingleton L v hv ν hprimitive).measure_preimage
    ((hC.preimage continuous_subtype_val.measurable).nullMeasurableSet)
  exact h.symm

end Measure

end ActualLine

end ArakelovGeometry.GeometryOfNumbers.PrimitiveLineMeasure

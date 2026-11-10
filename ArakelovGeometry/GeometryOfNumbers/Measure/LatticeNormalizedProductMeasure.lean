/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.Measure.LatticeNormalizedMeasure

/-! # The actual normalized Haar measure of a product lattice -/

@[expose] public section

noncomputable section
open Module MeasureTheory MeasureTheory.Measure Set

namespace ArakelovGeometry.GeometryOfNumbers

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- The actual normalized measure in an actual lattice basis is its canonical basis Haar measure. -/
theorem latticeNormalizedMeasure_span_basis {ι : Type*} [Fintype ι]
    (b : Basis ι ℝ E) (μ : Measure E) [IsAddHaarMeasure μ] :
    latticeNormalizedMeasure (Submodule.span ℤ (Set.range b)) μ = b.addHaar := by
  apply latticeNormalizedMeasure_eq_of_domain_measure_one _ μ b.addHaar
    (ZSpan.isAddFundamentalDomain b b.addHaar)
  exact (measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b b.addHaar)).trans
    b.addHaar_self

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- The actual integer span of a product basis is the product of its integer spans. -/
theorem integerSpan_prod_basis {ι κ : Type*}
    (b : Basis ι ℝ E) (c : Basis κ ℝ F) :
    Submodule.span ℤ (Set.range (b.prod c)) =
      (Submodule.span ℤ (Set.range b)).prod (Submodule.span ℤ (Set.range c)) := by
  classical
  ext x
  change x ∈ Submodule.span ℤ (Set.range (b.prod c)) ↔
    x.1 ∈ Submodule.span ℤ (Set.range b) ∧ x.2 ∈ Submodule.span ℤ (Set.range c)
  rw [(b.prod c).mem_span_iff_repr_mem ℤ, b.mem_span_iff_repr_mem ℤ,
    c.mem_span_iff_repr_mem ℤ]
  constructor
  · intro h
    exact ⟨fun i => h (Sum.inl i), fun j => h (Sum.inr j)⟩
  · rintro ⟨hb, hc⟩ (i | j)
    · exact hb i
    · exact hc j

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (M : Submodule ℤ F) [DiscreteTopology M] [IsZLattice ℝ M]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Discreteness of the actual product lattice is derived in its canonical topology. -/
theorem latticeProduct_discrete : DiscreteTopology (L.prod M) := by
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  let c := (Module.Free.chooseBasis ℤ M).ofZLatticeBasis ℝ M
  have hspan : Submodule.span ℤ (Set.range (b.prod c)) = L.prod M := by
    rw [integerSpan_prod_basis, (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ,
      (Module.Free.chooseBasis ℤ M).ofZLatticeBasis_span ℝ]
  rw [← hspan]
  infer_instance

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Fullness of the actual product lattice is derived from actual component lattice bases. -/
theorem latticeProduct_isZLattice :
    letI : DiscreteTopology (L.prod M) := latticeProduct_discrete L M
    IsZLattice ℝ (L.prod M) := by
  let : DiscreteTopology (L.prod M) := latticeProduct_discrete L M
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  let c := (Module.Free.chooseBasis ℤ M).ofZLatticeBasis ℝ M
  have hspan : Submodule.span ℤ (Set.range (b.prod c)) = L.prod M := by
    rw [integerSpan_prod_basis, (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ,
      (Module.Free.chooseBasis ℤ M).ofZLatticeBasis_span ℝ]
  constructor
  rw [← hspan]
  exact ZSpan.span_top (b.prod c)

/-- The actual covolume-normalized measure of the actual product lattice is the product measure. -/
theorem latticeNormalizedMeasure_prod (μ : Measure E) [IsAddHaarMeasure μ]
    (ν : Measure F) [IsAddHaarMeasure ν] :
    latticeNormalizedMeasure (L.prod M) (μ.prod ν) =
      (latticeNormalizedMeasure L μ).prod (latticeNormalizedMeasure M ν) := by
  let : DiscreteTopology (L.prod M) := latticeProduct_discrete L M
  let : IsZLattice ℝ (L.prod M) := latticeProduct_isZLattice L M
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  let c := (Module.Free.chooseBasis ℤ M).ofZLatticeBasis ℝ M
  have hspan : Submodule.span ℤ (Set.range (b.prod c)) = L.prod M := by
    rw [integerSpan_prod_basis, (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ,
      (Module.Free.chooseBasis ℤ M).ofZLatticeBasis_span ℝ]
  have hF : IsAddFundamentalDomain (L.prod M) (ZSpan.fundamentalDomain (b.prod c))
      (b.prod c).addHaar := by
    rw [← hspan]
    exact ZSpan.isAddFundamentalDomain (b.prod c) (b.prod c).addHaar
  have hFone : (b.prod c).addHaar (ZSpan.fundamentalDomain (b.prod c)) = 1 :=
    (measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped (b.prod c)
      (b.prod c).addHaar)).trans (b.prod c).addHaar_self
  have hb : latticeNormalizedMeasure L μ = b.addHaar := by
    have hL := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ
    calc
      _ = latticeNormalizedMeasure (Submodule.span ℤ (Set.range b)) μ :=
        congrArg (fun N : Submodule ℤ E => latticeNormalizedMeasure N μ) hL.symm
      _ = _ := latticeNormalizedMeasure_span_basis b μ
  have hc : latticeNormalizedMeasure M ν = c.addHaar := by
    have hM := (Module.Free.chooseBasis ℤ M).ofZLatticeBasis_span ℝ
    calc
      _ = latticeNormalizedMeasure (Submodule.span ℤ (Set.range c)) ν :=
        congrArg (fun N : Submodule ℤ F => latticeNormalizedMeasure N ν) hM.symm
      _ = _ := latticeNormalizedMeasure_span_basis c ν
  calc
    _ = (b.prod c).addHaar := latticeNormalizedMeasure_eq_of_domain_measure_one
      (L.prod M) (μ.prod ν) (b.prod c).addHaar hF hFone
    _ = b.addHaar.prod c.addHaar := b.prod_addHaar c
    _ = _ := by rw [hb, hc]

end ArakelovGeometry.GeometryOfNumbers

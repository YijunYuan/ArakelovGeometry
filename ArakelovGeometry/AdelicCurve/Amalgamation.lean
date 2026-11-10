/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Defs
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.Combinatorics.Matroid.Init

/-!
# Amalgamation of adelic structures

The amalgamation of two adelic structures on the same field `K` (Chen–Moriwaki, §3.2): the
disjoint union of the index spaces, carrying the sum measure and the two families of
absolute values.  Properness is preserved: the product formula for the amalgamation is the
sum of the two product formulas.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure

open MeasureTheory

/-- The left inclusion of a measurable disjoint union is a measurable embedding. -/
theorem measurableEmbedding_inl {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] : MeasurableEmbedding (@Sum.inl α β) :=
  ⟨Sum.inl_injective, measurable_inl, fun _ hs ↦ hs.inl_image⟩

/-- The right inclusion of a measurable disjoint union is a measurable embedding. -/
theorem measurableEmbedding_inr {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] : MeasurableEmbedding (@Sum.inr α β) :=
  ⟨Sum.inr_injective, measurable_inr, fun _ hs ↦ hs.inr_image⟩

/-- The amalgamation of two adelic structures on `K`: the disjoint union of the index
spaces, with the sum measure and the two families of absolute values. -/
noncomputable def amalgamation {K : Type*} [Field K] (AS1 AS2 : AdelicStructure K) :
    AdelicStructure K where
  Ω := AS1.Ω ⊕ AS2.Ω
  A := Sum.instMeasurableSpace
  v := AS1.v.map Sum.inl + AS2.v.map Sum.inr
  ϕ := Sum.elim AS1.ϕ AS2.ϕ
  measurable_log x hx := measurable_fun_sum (AS1.measurable_log x hx) (AS2.measurable_log x hx)
  integrable_log x hx := integrable_add_measure.mpr
    ⟨measurableEmbedding_inl.integrable_map_iff.mpr (AS1.integrable_log x hx),
      measurableEmbedding_inr.integrable_map_iff.mpr (AS2.integrable_log x hx)⟩

/-- Notation for the `amalgamation` of two adelic structures over `K`.

This matches Mathlib's `⨿` (binary categorical coproduct); when both notations are in
scope they are disambiguated by the operand type, since `amalgamation` acts on
`AdelicStructure K`. -/
scoped notation:20 AS1 " ⨿ " AS2:20 => amalgamation AS1 AS2

/-- The amalgamation of two proper adelic structures is proper: the product formula for the
amalgamation is the sum of the two product formulas. -/
theorem isProper_amalgamation {K : Type*} [Field K] (AS1 AS2 : AdelicStructure K)
    [AS1.IsProper] [AS2.IsProper] :
    (AS1 ⨿ AS2).IsProper := by
  constructor
  intro x hx
  have e1 : ∫ ω, Real.log ((AS1.ϕ ω) x) ∂AS1.v = 0 :=
    IsProper.product_formula (AS := AS1) x hx
  have e2 : ∫ ω, Real.log ((AS2.ϕ ω) x) ∂AS2.v = 0 :=
    IsProper.product_formula (AS := AS2) x hx
  have key : ∫ ω, Real.log ((Sum.elim AS1.ϕ AS2.ϕ ω) x)
      ∂(AS1.v.map Sum.inl + AS2.v.map Sum.inr) = 0 := by
    rw [integral_add_measure
        (measurableEmbedding_inl.integrable_map_iff.mpr (AS1.integrable_log x hx))
        (measurableEmbedding_inr.integrable_map_iff.mpr (AS2.integrable_log x hx)),
      measurableEmbedding_inl.integral_map, measurableEmbedding_inr.integral_map]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [e1, e2, add_zero]
  exact key

end ArakelovGeometry.AdelicStructure

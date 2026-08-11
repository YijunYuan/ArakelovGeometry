import ArakelovGeometry.AdelicCurve.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Coproducts

namespace ArakelovGeometry.AdelicStructure

open MeasureTheory

private theorem measurableEmbedding_inl {α : Type u_1} {β : Type u_2} [MeasurableSpace α]
  [MeasurableSpace β] : MeasurableEmbedding (@Sum.inl α β) :=
  ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩

private theorem measurableEmbedding_inr {α : Type u_1} {β : Type u_2} [MeasurableSpace α]
  [MeasurableSpace β] : MeasurableEmbedding (@Sum.inr α β) :=
  ⟨Sum.inr_injective, measurable_inr, fun _ hs => hs.inr_image⟩

open CategoryTheory.Limits in
noncomputable def Amalgamation {K : Type u_1} [Field K] (AS1 AS2 : AdelicStructure K) :
  AdelicStructure K where
    Ω := AS1.Ω ⊕ AS2.Ω
    A := Sum.instMeasurableSpace
    v := AS1.v.map Sum.inl + AS2.v.map Sum.inr
    ϕ := Sum.elim AS1.ϕ AS2.ϕ
    hφ1 x hx := measurable_fun_sum (AS1.hφ1 x hx) (AS2.hφ1 x hx)
    hφ2 x hx := integrable_add_measure.mpr
      ⟨measurableEmbedding_inl.integrable_map_iff.mpr (AS1.hφ2 x hx),
        measurableEmbedding_inr.integrable_map_iff.mpr (AS2.hφ2 x hx)⟩

/-- Notation for the `Amalgamation` of two adelic structures over `K`.

This overloads Mathlib's `⨿` (binary categorical coproduct); the two are disambiguated by
the operand type, since `Amalgamation` acts on `AdelicStructure K`. -/
scoped notation:20 AS1 " ⨿ " AS2:20 => Amalgamation AS1 AS2

open ArakelovGeometry.AdelicCurve in
theorem IsProper_of_amalgamation {K : Type u_1} [Field K] (AS1 AS2 : AdelicStructure K)
  [IsProper AS1.toAdelicCurve] [IsProper AS2.toAdelicCurve] :
  IsProper (AS1 ⨿ AS2).toAdelicCurve := by
  constructor
  intro x hx
  have e1 : ∫ ω, Real.log ((AS1.ϕ ω) x) ∂AS1.v = 0 :=
    IsProper.product_formula (C := AS1.toAdelicCurve) x hx
  have e2 : ∫ ω, Real.log ((AS2.ϕ ω) x) ∂AS2.v = 0 :=
    IsProper.product_formula (C := AS2.toAdelicCurve) x hx
  have key : ∫ ω, Real.log ((Sum.elim AS1.ϕ AS2.ϕ ω) x)
      ∂(AS1.v.map Sum.inl + AS2.v.map Sum.inr) = 0 := by
    rw [integral_add_measure
        (measurableEmbedding_inl.integrable_map_iff.mpr (AS1.hφ2 x hx))
        (measurableEmbedding_inr.integrable_map_iff.mpr (AS2.hφ2 x hx)),
      measurableEmbedding_inl.integral_map, measurableEmbedding_inr.integral_map]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [e1, e2, add_zero]
  exact key

end ArakelovGeometry.AdelicStructure

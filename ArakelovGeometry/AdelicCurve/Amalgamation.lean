import ArakelovGeometry.AdelicCurve.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Coproducts

namespace ArakelovGeometry.AdelicStructure

open CategoryTheory.Limits in
noncomputable def Amalgamation {K : Type u_1} [Field K] (AS1 AS2 : AdelicStructure K) :
  AdelicStructure K where
    Ω := AS1.Ω ⊕ AS2.Ω
    A := Sum.instMeasurableSpace
    v := MeasureTheory.Measure.sum id
    ϕ := Sum.elim AS1.ϕ AS2.ϕ
    hφ1 := sorry
    hφ2 := sorry

open ArakelovGeometry.AdelicCurve in
theorem IsProper_of_amalgamation {K : Type u_1} [Field K] (AS1 AS2 : AdelicStructure K)
  [IsProper AS1.toAdelicCurve] [IsProper AS2.toAdelicCurve] :
  IsProper (Amalgamation AS1 AS2).toAdelicCurve := by
  sorry

end ArakelovGeometry.AdelicStructure

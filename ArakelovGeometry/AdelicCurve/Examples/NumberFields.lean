import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.ExternalResults.Place
import ArakelovGeometry.ExternalResults.AbsoluteValue
import ArakelovGeometry.ExternalResults.Measure
import
Mathlib.NumberTheory.NumberField.ProductFormula

namespace ArakelovGeometry.AdelicCurve

open MeasureTheory

#check NumberField.prod_abs_eq_one
noncomputable def NumberFieldAdelicStructure (K : Type u_1) [Field K] [NumberField K] :
    AdelicStructure K where
  Ω := Place K
  A := ⊤
  v := @Measure.ofSingletons _ ⊤ (fun ω => ω.out.localDegree ℚ)
  ϕ := Quotient.out
  hφ1 := fun x _ => measurable_from_top
  hφ2 := sorry

end ArakelovGeometry.AdelicCurve

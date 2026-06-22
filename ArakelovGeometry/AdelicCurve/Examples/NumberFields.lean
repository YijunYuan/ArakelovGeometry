import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.ExternalResults.Place

namespace ArakelovGeometry.AdelicCurve

open MeasureTheory
open ArakelovGeometry.ExternalResults

noncomputable def NumberFieldAdelicStructure (K : Type u_1) [Field K] [NumberField K] :
  AdelicStructure K where
  Ω := Place K
  A := {
    MeasurableSet' := fun _ => True
    measurableSet_empty := by simp
    measurableSet_compl := by simp
    measurableSet_iUnion := by simp
  }
  v := sorry
  ϕ v := v.out
  hφ1 := sorry
  hφ2 := sorry

end ArakelovGeometry.AdelicCurve

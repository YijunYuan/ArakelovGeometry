import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.ExternalResults.Place
import ArakelovGeometry.ExternalResults.AbsoluteValue
import ArakelovGeometry.ExternalResults.Measure
import
Mathlib.NumberTheory.NumberField.ProductFormula

namespace ArakelovGeometry.AdelicStructure

open MeasureTheory AbsoluteValue NumberField
open scoped ENNReal

/-! ### The number-field adelic structure (`thm:numberfield_integrable`)

The integrability obligation `hφ2` reduces, via the Dirac-sum criterion
`MeasureTheory.integrable_sum_dirac_iff`, to summability of
`ω ↦ (localDegree ω : ℝ) * ‖log (ω.out x)‖`, which has finite support by
`finite_out_ne_one`. -/

noncomputable def NumberFieldAdelicStructure (K : Type u_1) [Field K] [NumberField K] :
    AdelicStructure K where
  Ω := AbsoluteValue.Place K
  A := ⊤
  v := @Measure.ofSingletons _ ⊤ (fun ω => ω.out.localDegree ℚ)
  ϕ := Quotient.out
  hφ1 := fun x _ => measurable_from_top
  hφ2 := by
    intro x hx
    letI : MeasurableSpace (AbsoluteValue.Place K) := ⊤
    -- The Dirac-sum integrability criterion, with weights `c ω = (localDegree ω : ℝ≥0∞)`
    -- and `x = id`. The ambient measure `ofSingletons c` is *definitionally*
    -- `Measure.sum (fun a => c a • dirac a)`, so the final `exact` only needs a cheap
    -- structural defeq (it does NOT evaluate `localDegree`).
    have hiff := integrable_sum_dirac_iff (ι := AbsoluteValue.Place K)
      (X := AbsoluteValue.Place K) (E := ℝ) (x := id)
      (c := fun ω => ((ω.out.localDegree ℚ : ℕ) : ℝ≥0∞))
      (f := fun ω => Real.log ((ω.out : AbsoluteValue K ℝ) x))
      (fun i => ENNReal.natCast_ne_top _)
    -- Reduce to: summability of `ω ↦ (localDegree ω : ℝ) * ‖log (ω.out x)‖`.
    refine hiff.mpr ?_
    apply summable_of_hasFiniteSupport
    -- The support is contained in the finite set `{ω | ω.out x ≠ 1}`.
    apply Set.Finite.subset (finite_out_ne_one (K := K) hx)
    intro ω hω
    simp only [Function.mem_support, id_eq, Set.mem_setOf_eq] at hω ⊢
    -- If `ω.out x = 1`, then `log (ω.out x) = 0`, so the summand is `0`.
    intro hc
    apply hω
    rw [hc, Real.log_one, norm_zero, mul_zero]

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.AdelicCurve
open ArakelovGeometry.AdelicStructure
noncomputable abbrev NumberFieldAdelicCurve (K : Type u_1) [Field K] [NumberField K]
  := (NumberFieldAdelicStructure K).toAdelicCurve

noncomputable instance (K : Type u_1) [Field K] [NumberField K] :
  IsProper (NumberFieldAdelicCurve K) := by
  sorry

end ArakelovGeometry.AdelicCurve

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.ExternalResults.AbsoluteValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ArakelovGeometry

open MeasureTheory AbsoluteValue

structure AdelicStructure (K : Type u_1) [Field K] where
  Ω : Type u_2 -- The underlying set of the measurable space
  [A : MeasurableSpace Ω] -- The σ-algebra on Ω
  v : Measure Ω -- The measure on the measurable space
  ϕ : Ω → AbsoluteValue K ℝ -- The function assigning an absolute value to each point in Ω
  hφ1 : ∀ x : K, x ≠ 0 → Measurable (fun (ω : Ω) => Real.log ((ϕ ω) x))
  hφ2 : ∀ x : K, x ≠ 0 → Integrable (fun (ω : Ω) => Real.log ((ϕ ω) x)) v

namespace AdelicStructure

instance instMeasurableSpaceΩ {K : Type u_1} [Field K] (AS : AdelicStructure K) :
  MeasurableSpace AS.Ω := AS.A

def Ωfin {K : Type u_1} [Field K] (AS : AdelicStructure K) : Set AS.Ω :=
  { ω : AS.Ω | IsNonarchimedean (AS.ϕ ω) }

def Ωinf {K : Type u_1} [Field K] (AS : AdelicStructure K) : Set AS.Ω :=
  { ω : AS.Ω | ¬ IsNonarchimedean (AS.ϕ ω) }

open Classical in
noncomputable def κ {K : Type u_1} [Field K] (AS : AdelicStructure K) (ω : AS.Ω) : ℝ :=
  if hω : ω ∈ AS.Ωinf then (exists_rpow_eq_of_archimedean_abs (AS.ϕ ω) hω.out).choose
  else 0

theorem κ_mem_Icc {K : Type u_1} [Field K] (AS : AdelicStructure K) (ω : AS.Ω) :
  AS.κ ω ∈ Set.Icc 0 1 := by
  by_cases hω : ω ∈ AS.Ωinf
  · unfold κ
    rw [dif_pos hω]
    exact Set.mem_Icc_of_Ioc (exists_rpow_eq_of_archimedean_abs (AS.ϕ ω) hω.out).choose_spec.1
  · simp [κ,hω]

theorem κ_eq_zero_iff {K : Type u_1} [Field K] (AS : AdelicStructure K) (ω : AS.Ω) :
  AS.κ ω = 0 ↔ ω ∈ AS.Ωfin := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · suffices h : ¬ ω ∈ AS.Ωinf by
      simp only [Ωinf, Set.mem_setOf_eq, not_not, Ωfin] at *
      exact h
    by_contra hc
    unfold κ at h
    rw [dif_pos hc] at h
    have := (exists_rpow_eq_of_archimedean_abs (AS.ϕ ω) hc.out).choose_spec.1.out.1
    linarith
  · have : ¬ ω ∈ AS.Ωinf := id fun hc ↦ hc h
    simp [κ, this]

theorem κ_def {K : Type u_1} [Field K] (AS : AdelicStructure K) {ω : AS.Ω} (hω : ω ∈ AS.Ωinf) :
  ∀ q : ℚ, AS.ϕ ω q = (Rat.AbsoluteValue.real q) ^ (AS.κ ω) := by
  have := (exists_rpow_eq_of_archimedean_abs (AS.ϕ ω) hω.out).choose_spec.2
  unfold κ
  rwa [dif_pos hω]

end AdelicStructure

structure AdelicCurve where
  K : Type u_1
  [hK : Field K]
  AS : AdelicStructure.{u_1, u_2} K

namespace AdelicCurve
instance instFieldK {C : AdelicCurve} : Field C.K := C.hK

abbrev Ω (C : AdelicCurve) := C.AS.Ω
abbrev v (C : AdelicCurve) := C.AS.v
abbrev ϕ (C : AdelicCurve) := C.AS.ϕ
noncomputable abbrev κ (C : AdelicCurve) := C.AS.κ
abbrev Ωfin (C : AdelicCurve) := C.AS.Ωfin
abbrev Ωinf (C : AdelicCurve) := C.AS.Ωinf

-- An adelic curve is `proper` if the product formula holds for all nonzero elements of K.
class IsProper (C : AdelicCurve) where
  product_formula : ∀ x : C.K, x ≠ 0 → ∫ ω, Real.log ((C.AS.ϕ ω) x) ∂C.AS.v = 0

end AdelicCurve

end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.PrimeIndexing
import ArakelovGeometry.NumberTheory.NumberField.Local.Prime.Pole

/-!
# Finite generation of actual integer prime-bound modules

The accepted countability-free integer-sequence criterion is transported by
the produced bijection with all actual source-normalized finite places.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ArakelovGeometry.FiniteValuation

open AdelicStructure ActualPrimeIndexing

variable {K : Type*} [Field K] [NumberField K]

/-- The full integer-sequence criterion at every actual source-normalized finite place. -/
theorem fg_normalizedFinitePlace_valuationModule_iff
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ) :
    (valuationModule (K := K) (fun p => b (normalizedPrimeEquivFinite p))).FG ↔
      {ω | 0 < b ω}.Finite ∨ {ω | b ω < 0}.Infinite := by
  let e := normalizedPrimeEquivFinite (K := K)
  have hfinite (s : Set (normalizedNumberFieldAdelicStructure K).Ωfin) :
      (e ⁻¹' s).Finite ↔ s.Finite :=
    ⟨fun h => h.of_preimage e.surjective, fun h => h.preimage e.injective.injOn⟩
  have hpos : {p | 0 < b (e p)}.Finite ↔ {ω | 0 < b ω}.Finite :=
    hfinite {ω | 0 < b ω}
  have hneg : {p | b (e p) < 0}.Infinite ↔ {ω | b ω < 0}.Infinite :=
    not_congr (hfinite {ω | b ω < 0})
  exact fg_valuationModule_iff.trans (or_congr hpos hneg)

/-- Infinitely many negative actual finite-place bounds force the genuine module to zero. -/
theorem normalizedFinitePlace_valuationModule_eq_bot_of_infinite_negative
    (b : (normalizedNumberFieldAdelicStructure K).Ωfin → ℤ)
    (hneg : {ω | b ω < 0}.Infinite) :
    valuationModule (K := K) (fun p => b (normalizedPrimeEquivFinite p)) = ⊥ := by
  apply valuationModule_eq_bot_of_infinite_negative
    (b := fun p => b (normalizedPrimeEquivFinite p))
  intro hfinite
  exact hneg (Set.Finite.of_preimage
    (f := normalizedPrimeEquivFinite (K := K)) (s := {ω | b ω < 0})
    hfinite normalizedPrimeEquivFinite.surjective)

end ArakelovGeometry.FiniteValuation

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Ring.Basic
import ArakelovGeometry.ExternalResults.Ostrowski

namespace ArakelovGeometry

open MeasureTheory

structure AdelicStructure (K : Type u_1) [Field K] where
  Ω : Type u_2 -- The underlying set of the measurable space
  [A : MeasurableSpace Ω] -- The σ-algebra on Ω
  v : Measure Ω -- The measure on the measurable space
  ϕ : Ω → AbsoluteValue K ℝ -- The function assigning an absolute value to each point in Ω
  hφ1 : ∀ x : K, x ≠ 0 → Measurable (fun (ω : Ω) => Real.log ((ϕ ω) x))
  hφ2 : ∀ x : K, x ≠ 0 → Integrable (fun (ω : Ω) => Real.log ((ϕ ω) x)) v

namespace AdelicStructure

def Ωfin {K : Type u_1} [Field K] (AS : AdelicStructure K) : Set AS.Ω :=
  { ω : AS.Ω | IsNonarchimedean (AS.ϕ ω) }

def Ωinf {K : Type u_1} [Field K] (AS : AdelicStructure K) : Set AS.Ω :=
  { ω : AS.Ω | ¬ IsNonarchimedean (AS.ϕ ω) }

-- Proposition 3.1.1
theorem Ωinf_measurable {K : Type u_1} [Field K] (AS : AdelicStructure K) :
  AS.A.MeasurableSet' AS.Ωinf := by
  sorry

end AdelicStructure

structure AdelicCurve where
  K : Type u_1
  [hK : Field K]
  AS : AdelicStructure.{u_1, u_2} K

namespace AdelicCurve
instance instFieldK {C : AdelicCurve} : Field C.K := C.hK

-- An adelic curve is `proper` if the product formula holds for all nonzero elements of K.
class IsProper (C : AdelicCurve) where
  product_formula : ∀ x : C.K, x ≠ 0 → ∫ ω, Real.log ((C.AS.ϕ ω) x) ∂C.AS.v = 0

end AdelicCurve

end ArakelovGeometry

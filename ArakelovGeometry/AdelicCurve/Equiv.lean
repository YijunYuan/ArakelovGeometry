/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Defs

/-!
# Equivalences of adelic structures

Measurable equivalences preserving absolute values and transporting the measure,
as used in the scalar-extension tower identities of Chen–Moriwaki, §3.4.

The `AdelicStructure` scope provides `S ≃ T` for equivalences of adelic structures
on the same field. Ordinary equivalences of types retain their usual meaning.
-/

namespace ArakelovGeometry

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u v w

/-- An equivalence between two adelic structures on the same field: a measurable equivalence
of the parameter spaces matching the families of absolute values and transporting one measure
to the other. This packages the meaning of the equalities of adelic curves in Chen–Moriwaki,
Proposition 3.4.4 and Theorem 3.4.12. -/
structure AdelicStructure.Equiv {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)
    (T : AdelicStructure.{u, w} K) where
  /-- The underlying measurable equivalence of parameter spaces. -/
  toMeasurableEquiv : S.Ω ≃ᵐ T.Ω
  /-- The equivalence matches the families of absolute values. -/
  ϕ_comp : ∀ x : S.Ω, T.ϕ (toMeasurableEquiv x) = S.ϕ x
  /-- The equivalence transports the measure of `S` to the measure of `T`. -/
  map_v : MeasureTheory.Measure.map toMeasurableEquiv S.v = T.v

namespace AdelicStructure

scoped infixl:25 " ≃ " => Equiv

end AdelicStructure

end ArakelovGeometry

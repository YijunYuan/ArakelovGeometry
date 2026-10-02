---
author: sync
content_type: theorem
created: '2026-10-02T14:15:48'
decl: ArakelovGeometry.AdelicCurve.RationalFunction.primeAbv_polynomial
docstring: On a polynomial the prime absolute value is the maximum of the coefficient
  absolute values.
file: ArakelovGeometry/AdelicCurve/Examples/RationalFunction/FinitePlaces.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicCurve.RationalFunction.primeAbv_polynomial
type: lean
updated: '2026-10-02T14:15:48'
---
theorem primeAbv_polynomial (p : Nat.Primes) (P : ℚ[X]) :
    primeAbv p (algebraMap ℚ[X] (RatFunc ℚ) P) =
      Polynomial.gaussNorm (rationalPadicAbv p) 1 P := by
  change ((primeValuation p (algebraMap ℚ[X] (RatFunc ℚ) P) : ℝ≥0) : ℝ) = _
  exact congrArg (fun a : ℝ≥0 ↦ (a : ℝ))
    (Valuation.extendToLocalization_apply_map_apply (primePolynomialValuation p) _ (RatFunc ℚ) P)
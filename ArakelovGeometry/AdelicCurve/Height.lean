/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Height.Basic
import ArakelovGeometry.AdelicCurve.Height.Affine
import ArakelovGeometry.AdelicCurve.Height.Extension
import ArakelovGeometry.AdelicCurve.Height.Polynomial
import ArakelovGeometry.AdelicCurve.Height.MinimalPolynomial
import ArakelovGeometry.AdelicCurve.Height.Northcott
import ArakelovGeometry.AdelicCurve.Height.Projective
import ArakelovGeometry.AdelicCurve.Height.ProjectiveNorthcott
import ArakelovGeometry.AdelicCurve.Height.FiniteExtension

/-!
# Height functions and Northcott finiteness

Import entry point for Chen–Moriwaki, Section 3.5:
tuple and projective heights, the Northcott property, extension and conjugate
invariance, polynomial estimates, affine and projective Northcott finiteness,
and preservation of the Northcott property under finite extension.
-/

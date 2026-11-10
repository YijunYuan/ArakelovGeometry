/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Height.Affine
public import ArakelovGeometry.AdelicCurve.Height.Basic
public import ArakelovGeometry.AdelicCurve.Height.Extension
public import ArakelovGeometry.AdelicCurve.Height.FiniteExtension
public import ArakelovGeometry.AdelicCurve.Height.MinimalPolynomial
public import ArakelovGeometry.AdelicCurve.Height.Northcott
public import ArakelovGeometry.AdelicCurve.Height.Polynomial
public import ArakelovGeometry.AdelicCurve.Height.Projective
public import ArakelovGeometry.AdelicCurve.Height.ProjectiveNorthcott
import Mathlib.CategoryTheory.Category.Init

/-!
# Height functions and Northcott finiteness

Import entry point for Chen–Moriwaki, Section 3.5:
tuple and projective heights, the Northcott property, extension and conjugate
invariance, polynomial estimates, affine and projective Northcott finiteness,
and preservation of the Northcott property under finite extension.
-/

@[expose] public section

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.Linearization
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Actual binary special-linear orbit coordinates

For Bost p31 the required implication is polynomial orbit closure to a DVR
specialization of the actual binary group action. We construct the coordinate
algebra of two determinant-one matrices. The polynomial parameterization uses
`h ↦ rhoDual (h⁻¹) f`; inversion is a bijection, so its image is exactly the
usual actual orbit. No reducedness or closed-point density is needed.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace ArakelovGeometry.InvariantTheory

end ArakelovGeometry.InvariantTheory

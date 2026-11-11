/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.OrbitSeparation
public import ArakelovGeometry.InvariantTheory.BinaryNegativeFiltration

/-!
# Actual binary geometric instability over an algebraically closed field

This is the binary, one-way implication required on Bost page 31. Quotient
Plücker nonsemistability produces actual centered negative real filtrations.
Factor coordinates are transported with the matrix/module SL group isomorphism,
and the actual quotient determinant is retained through orbit separation, DVR
degeneration and residue polynomial descent. Original-field optimizer descent
is the separate consumer in `Trivial.Filtration.Instability`.
-/

@[expose] public section

open scoped TensorProduct
open Module

noncomputable section

namespace ArakelovGeometry.InvariantTheory

end ArakelovGeometry.InvariantTheory

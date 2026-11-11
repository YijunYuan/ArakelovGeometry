/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.BinaryInstability
public import ArakelovGeometry.InvariantTheory.BinaryTensorTransport

/-!
# Actual original-field negative filtrations from binary geometric instability

For the unstable case on Bost page 31, geometric nonsemistability of the same
scalar-extended quotient yields centered finite left-continuous real filtrations
over the original characteristic-zero field, with negative actual quotient
expectation and total energy one. The algebraic closure may have infinite
degree. Galois stability is obtained from uniqueness of the optimizer by the
existing rationality theorem; neither stability nor a negative candidate is an
input. This one-way binary implication supplies A9's optimizer input. The
subsequent adelic degree inequality and Bost rank induction are separate.
-/

@[expose] public section

open scoped TensorProduct
open Module ArakelovGeometry ArakelovGeometry.InvariantTheory

noncomputable section

namespace Submodule

end Submodule

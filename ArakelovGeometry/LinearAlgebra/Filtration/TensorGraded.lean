/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.Graded
public import ArakelovGeometry.LinearAlgebra.Filtration.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Canonical graded tensor maps

Tensoring the two step inclusions and then taking the quotient gives a map
from each pair of grades into the grade at their total weight. The source of
the assembled map retains every pair with that total weight.
-/

@[expose] public section

open scoped TensorProduct

namespace Submodule

variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]

end Submodule

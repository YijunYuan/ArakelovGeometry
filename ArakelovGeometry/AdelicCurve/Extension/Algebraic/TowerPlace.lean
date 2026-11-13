/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import Mathlib.CategoryTheory.Category.Init

/-!
# Places in a tower of algebraic extensions

The place of a successive extension determines a place of the direct extension.
Its final absolute value is unchanged; compatibility with the base follows from
the scalar-tower identity. This construction is independent of vector bundles.
-/

@[expose] public section

namespace ArakelovGeometry

universe u w

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]

/-- The direct extension place attached to a place in a successive field
extension. Its absolute value is unchanged. -/
def scalarExtensionTowerPlace {S : AdelicStructure K}
    [Algebra.IsAlgebraic K L] {M : Type*} [Field M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) M) :
    AdelicStructure.ParameterSpaceExtension S M where
  base := x.base.base
  abv := x.abv
  restrict_eq := by
    ext a
    change x.abv (algebraMap K M a) = S.ϕ x.base.base a
    rw [IsScalarTower.algebraMap_apply K L M]
    exact (congrArg (fun f : AbsoluteValue L ℝ ↦ f (algebraMap K L a)) x.restrict_eq).trans
      (congrArg (fun f : AbsoluteValue K ℝ ↦ f a) x.base.restrict_eq)

end ArakelovGeometry

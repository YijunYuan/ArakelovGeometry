/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Absolute.CompatibleTower

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Isomorphism.VectorDegree
import Mathlib.CategoryTheory.Category.Init
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Actual absolute minima through an arbitrary external algebraic middle field

The original canonical absolute minimum equals the minimum of the genuine
iterated closure bundle whose analytic fields were produced from the original
curve. The legacy absolute-minimum API on the intermediate ordinary bundle is
identified only when its intermediate regularity is independently supplied.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v wL wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  [hreg : S.HasRegularBase]
  [hN : S.IsArchimedeanNormalized]

/-- The canonical original absolute minimum equals the actual minimum of the
produced iterated closure bundle, with no intermediate regularity assumption. -/
theorem absoluteLogarithmicMinimum_eq_ordinaryCompatibleTower (i : ℕ) :
    V.absoluteLogarithmicMinimum i =
      (V.ordinaryCompatibleTower (L := L) (M := AlgebraicClosure L)).logarithmicMinimum i :=
  (V.absoluteLogarithmicMinimum_eq_commonClosure (L := L) i).trans
    (V.ordinaryCompatibleTower_logarithmicMinimum (L := L)
      (M := AlgebraicClosure L) i).symm

/-- The actual absolute first minimum equals the genuine nested first minimum,
including the rank-zero bottom convention. -/
theorem absoluteMaximalLogarithmicMinimum_eq_ordinaryCompatibleTower :
    V.absoluteMaximalLogarithmicMinimum =
      (V.ordinaryCompatibleTower (L := L) (M := AlgebraicClosure L)
).maximalLogarithmicMinimum :=
  V.absoluteLogarithmicMinimum_eq_ordinaryCompatibleTower (L := L) 1

/-- The actual absolute last minimum equals the genuine nested last minimum;
successive scalar extension preserves its rank index even at rank zero. -/
theorem absoluteMinimalLogarithmicMinimum_eq_ordinaryCompatibleTower :
    V.absoluteMinimalLogarithmicMinimum =
      (V.ordinaryCompatibleTower (L := L) (M := AlgebraicClosure L)
).minimalLogarithmicMinimum := by
  unfold absoluteMinimalLogarithmicMinimum minimalLogarithmicMinimum
  rw [V.absoluteLogarithmicMinimum_eq_ordinaryCompatibleTower (L := L)]
  rw [Module.finrank_baseChange, Module.finrank_baseChange]

/-- Exact overlap with the legacy API on the actual ordinary intermediate
bundle, only when its regularity is independently given. Normalization is
produced from the original curve. -/
theorem absoluteLogarithmicMinimum_ordinaryScalarExtension_eq
    [hregL : (S.algebraicExtension L).HasRegularBase] (i : ℕ) :
    (V.ordinaryScalarExtension (L := L)).absoluteLogarithmicMinimum
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) i =
        V.absoluteLogarithmicMinimum i := by
  change ((V.ordinaryScalarExtension (L := L)).ordinaryScalarExtension
      (L := AlgebraicClosure L)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension
          (L := L))⟩)).logarithmicMinimum i = _
  have hB : (V.ordinaryScalarExtension (L := L)).ordinaryScalarExtension
      (L := AlgebraicClosure L)
      (hN := ⟨(AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L))⟩) =
        V.ordinaryCompatibleTower (L := L) (M := AlgebraicClosure L) := rfl
  rw [hB]
  exact (V.absoluteLogarithmicMinimum_eq_ordinaryCompatibleTower (L := L) i).symm

end ArakelovGeometry.AdelicVectorBundle

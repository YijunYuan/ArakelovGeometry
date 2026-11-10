/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.CompatibleTowerLogarithmicMinima
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionIsomorphismVectorDegree

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
  (hreg : S.HasCommonCountableDenseSubfield ∨
    (Countable S.Ω ∧ DiscreteMeasurableSpace S.Ω) ∨
    (MeasurableSingletonClass S.Ω ∧ (∀ ω, 0 < S.v {ω}) ∧ ∀ ω, ω ∈ S.Ωfin))
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The canonical original absolute minimum equals the actual minimum of the
produced iterated closure bundle, with no intermediate regularity assumption. -/
theorem absoluteLogarithmicMinimum_eq_ordinaryCompatibleTower (i : ℕ) :
    V.absoluteLogarithmicMinimum hreg hN i =
      (V.ordinaryCompatibleTower (L := L) (M := AlgebraicClosure L) hreg hN).logarithmicMinimum i :=
  (V.absoluteLogarithmicMinimum_eq_commonClosure (L := L) hreg hN i).trans
    (V.ordinaryCompatibleTower_logarithmicMinimum (L := L)
      (M := AlgebraicClosure L) hreg hN i).symm

/-- The actual absolute first minimum equals the genuine nested first minimum,
including the rank-zero bottom convention. -/
theorem absoluteMaximalLogarithmicMinimum_eq_ordinaryCompatibleTower :
    V.absoluteMaximalLogarithmicMinimum hreg hN =
      (V.ordinaryCompatibleTower (L := L) (M := AlgebraicClosure L)
        hreg hN).maximalLogarithmicMinimum :=
  V.absoluteLogarithmicMinimum_eq_ordinaryCompatibleTower (L := L) hreg hN 1

/-- The actual absolute last minimum equals the genuine nested last minimum;
successive scalar extension preserves its rank index even at rank zero. -/
theorem absoluteMinimalLogarithmicMinimum_eq_ordinaryCompatibleTower :
    V.absoluteMinimalLogarithmicMinimum hreg hN =
      (V.ordinaryCompatibleTower (L := L) (M := AlgebraicClosure L)
        hreg hN).minimalLogarithmicMinimum := by
  unfold absoluteMinimalLogarithmicMinimum minimalLogarithmicMinimum
  rw [V.absoluteLogarithmicMinimum_eq_ordinaryCompatibleTower (L := L) hreg hN]
  rw [Module.finrank_baseChange, Module.finrank_baseChange]

/-- Exact overlap with the legacy API on the actual ordinary intermediate
bundle, only when its regularity is independently given. Normalization is
produced from the original curve. -/
theorem absoluteLogarithmicMinimum_ordinaryScalarExtension_eq
    (hregL : (S.algebraicExtension L).HasCommonCountableDenseSubfield ∨
      (Countable (S.algebraicExtension L).Ω ∧
        DiscreteMeasurableSpace (S.algebraicExtension L).Ω) ∨
      (MeasurableSingletonClass (S.algebraicExtension L).Ω ∧
        (∀ x, 0 < (S.algebraicExtension L).v {x}) ∧
        ∀ x, x ∈ (S.algebraicExtension L).Ωfin)) (i : ℕ) :
    (V.ordinaryScalarExtension (L := L) hreg hN).absoluteLogarithmicMinimum hregL
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) i =
        V.absoluteLogarithmicMinimum hreg hN i := by
  change ((V.ordinaryScalarExtension (L := L) hreg hN).ordinaryScalarExtension
      (L := AlgebraicClosure L) hregL
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)).logarithmicMinimum i = _
  have hB : (V.ordinaryScalarExtension (L := L) hreg hN).ordinaryScalarExtension
      (L := AlgebraicClosure L) hregL
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) =
        V.ordinaryCompatibleTower (L := L) (M := AlgebraicClosure L) hreg hN := rfl
  rw [hB]
  exact (V.absoluteLogarithmicMinimum_eq_ordinaryCompatibleTower (L := L) hreg hN i).symm

end ArakelovGeometry.AdelicVectorBundle

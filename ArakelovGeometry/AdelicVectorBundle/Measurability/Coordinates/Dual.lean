/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic

import ArakelovGeometry.AdelicVectorBundle.Dual.Restriction
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.MeasurableQuotient
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Measurable actual coordinate subspace and quotient duals

On an all-finite adelic curve, the actual dual-basis identity and annihilator
isometries combine with the produced measurable quotient theorem. Neither the
field nor the evaluation-generated parameter space is assumed countable.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.NormFamily

variable {K E m : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Fintype m]

omit [FiniteDimensional K E] in
private theorem ofBasis_eq_mixed_of_all_finite (b : Module.Basis m K E)
    [hS : S.HasOnlyFinitePlaces] :
    ofBasis S E b = ofBasisMixed S E b := by
  ext ω z
  exact (ofBasisMixed_norm_of_finite b ω (hS ω) z).symm

/-- The genuine completed dual of a coordinate maximum family is the dual-basis
coordinate maximum family when every place is non-Archimedean. -/
theorem ofBasis_dual_of_all_finite [DecidableEq m] (b : Module.Basis m K E)
    [hS : S.HasOnlyFinitePlaces] :
    (ofBasis S E b).dual = ofBasis S (Module.Dual K E) b.dualBasis := by
  rw [ofBasis_eq_mixed_of_all_finite (S := S) b, ofBasisMixed_dual]

/-- The actual coordinate dual family has measurable rational evaluations. -/
theorem ofBasis_dual_isMeasurable_of_all_finite (b : Module.Basis m K E)
    [hS : S.HasOnlyFinitePlaces] : (ofBasis S E b).dual.IsMeasurable := by
  classical
  rw [ofBasis_dual_of_all_finite b]
  exact ofBasis_isMeasurable b.dualBasis

/-- The canonical dual of every actual coordinate quotient is measurable. -/
theorem ofBasis_quotient_dual_isMeasurable_of_all_finite (b : Module.Basis m K E)
    (F : Submodule K E) [hS : S.HasOnlyFinitePlaces] :
    ((ofBasis S E b).quotient F).dual.IsMeasurable := by
  classical
  rw [(ofBasis S E b).quotient_dual_annihilator F]
  exact ((ofBasis_dual_isMeasurable_of_all_finite b).restrict F.dualAnnihilator).pullback
    F.dualQuotEquivDualAnnihilator.toLinearMap F.dualQuotEquivDualAnnihilator.injective

/-- The actual dual of every coordinate subspace restriction is measurable. -/
theorem ofBasis_restrict_dual_isMeasurable_of_all_finite (b : Module.Basis m K E)
    (F : Submodule K E) [hS : S.HasOnlyFinitePlaces] :
    ((ofBasis S E b).restrict F).dual.IsMeasurable := by
  classical
  have hξ : (ofBasis S E b).IsUltrametricAtFinitePlaces := by
    rw [ofBasis_eq_mixed_of_all_finite (S := S) b]
    exact ofBasisMixed_isUltrametricAtFinitePlaces b
  have harch : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion := by
    intro ω hω
    exact False.elim (hω (hS ω))
  have hm : ((ofBasis S E b).dual.quotient F.dualAnnihilator).IsMeasurable := by
    rw [ofBasis_dual_of_all_finite b]
    exact ofBasis_quotient_isMeasurable_of_all_finite b.dualBasis F.dualAnnihilator
  rw [(ofBasis S E b).dual_quotient_annihilator (hξ := hξ) (hS := ⟨harch⟩) F] at hm
  exact ((ofBasis S E b).restrict F).dual.isMeasurable_pullback_iff
    (Subspace.quotAnnihilatorEquiv F) |>.mp hm

end ArakelovGeometry.NormFamily

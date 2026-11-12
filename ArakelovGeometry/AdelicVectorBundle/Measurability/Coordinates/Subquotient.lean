/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic

import ArakelovGeometry.AdelicVectorBundle.Dual.Restriction
import ArakelovGeometry.AdelicVectorBundle.Measurability.Coordinates.Dual
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.MeasurableQuotient
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Quotient.Restriction
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Measurable actual coordinate subquotients

The canonical completed first-isomorphism isometry identifies a native
restriction followed by quotient with a restriction of an ambient quotient.
This consumes actual quotient measurability without counting the field or base.
-/

@[expose] public section

noncomputable section
namespace ArakelovGeometry.NormFamily

variable {K E m : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Fintype m]

/-- Every actual coordinate subquotient with ambient nested endpoints is
measurable on its original completed native quotient fibres. -/
theorem ofBasis_subquotient_isMeasurable_of_all_finite (b : Module.Basis m K E)
    (B T : Submodule K E) (hTB : T ≤ B) [hS : S.HasOnlyFinitePlaces] :
    (((ofBasis S E b).restrict B).quotient (T.comap B.subtype)).IsMeasurable := by
  let g := T.mkQ.comp B.subtype
  have hk : g.ker = T.comap B.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have he : ((ofBasis S E b).restrict B).quotient g.ker =
      (((ofBasis S E b).quotient T).restrict g.range).pullback
        g.quotKerEquivRange.toLinearMap g.quotKerEquivRange.injective := by
    ext ω z
    exact (ofBasis S E b).quotient_restrict_range_norm_eq B T hTB ω z
  rw [← hk, he]
  exact ((ofBasis_quotient_isMeasurable_of_all_finite b T).restrict g.range).pullback
    g.quotKerEquivRange.toLinearMap g.quotKerEquivRange.injective

/-- Every literal native quotient of every actual coordinate restriction is
measurable, including arbitrary relative subspaces and equal endpoints. -/
theorem ofBasis_restrict_quotient_isMeasurable_of_all_finite (b : Module.Basis m K E)
    (B : Submodule K E) (U : Submodule K B) [hS : S.HasOnlyFinitePlaces] :
    (((ofBasis S E b).restrict B).quotient U).IsMeasurable := by
  let T := U.map B.subtype
  have hTB : T ≤ B := by
    rintro _ ⟨u, _, rfl⟩
    exact u.property
  have hU : T.comap B.subtype = U := by
    rw [Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
  rw [← hU]
  exact ofBasis_subquotient_isMeasurable_of_all_finite b B T hTB

/-- The actual dual of every literal native coordinate subquotient is
measurable, without countability or chosen orthonormal basis hypotheses. -/
theorem ofBasis_restrict_quotient_dual_isMeasurable_of_all_finite (b : Module.Basis m K E)
    (B : Submodule K E) (U : Submodule K B) [hS : S.HasOnlyFinitePlaces] :
    (((ofBasis S E b).restrict B).quotient U).dual.IsMeasurable := by
  rw [((ofBasis S E b).restrict B).quotient_dual_annihilator U]
  exact ((ofBasis_restrict_dual_isMeasurable_of_all_finite b B).restrict
    U.dualAnnihilator).pullback
      U.dualQuotEquivDualAnnihilator.toLinearMap U.dualQuotEquivDualAnnihilator.injective

end ArakelovGeometry.NormFamily

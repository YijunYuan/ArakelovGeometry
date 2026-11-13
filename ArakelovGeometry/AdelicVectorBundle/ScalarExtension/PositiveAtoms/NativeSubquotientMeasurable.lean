/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Examples.FunctionFields
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.Measurability.Coordinates.Subquotient
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.AtomicNormComparison
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.ScalarExtensionExceptions
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.ScalarExtensionMeasurable

/-!
# Actual native subquotient regularity after finite geometric extension

Original dominated families agree with coordinates off one produced countable
base set. Actual restriction, quotient and dual-distance contractions transfer
coordinate regularity to every native relative quotient, without countability
of the constant field or parameter spaces.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

private theorem isMeasurable_of_countable_localDist_zero
    {F : Type*} [AddCommGroup F] [Module L F] [FiniteDimensional L F]
    [MeasurableSingletonClass (S.algebraicExtension L).Ω]
    (η θ : NormFamily (S.algebraicExtension L) F)
    [hθ : θ.IsMeasurable] (T : Set (S.algebraicExtension L).Ω) (hT : T.Countable)
    (he : ∀ x ∉ T, η.localDist θ x = 0) : η.IsMeasurable := by
  constructor
  intro z
  apply Measurable.measurable_of_countable_ne (hθ z)
  apply hT.mono
  intro x hx
  by_contra h
  have hn := (η.localDist_eq_zero_iff θ x).mp (he x h)
  exact hx (congrArg (fun n => n ((1 : x.abv.Completion) ⊗ₜ[L] z)) hn).symm

/-- Every actual native relative quotient of the finite scalar extension of
an original dominated family is measurable on an all-finite positive atomic
curve. The field and both parameter spaces may be uncountable. -/
theorem IsDominated.scalarExtension_restrict_quotient_isMeasurable_of_pos_singletons
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) [hpos : S.HasPositiveSingletons]
    [hS : S.HasOnlyFinitePlaces]
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).IsMeasurable := by
  let := AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
    (S := S) (L := L)
  let b := Module.finBasis K E
  have hfin := AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin (S := S)
  obtain ⟨H, _, _, hc, _, hb, _⟩ :=
    IsDominated.exists_scalarExtension_coordinate_exceptions_of_pos_singletons ξ b hξ hfin
  have ht := AdelicStructure.ParameterSpaceExtension.countable_preimage_proj_of_finiteDimensional
    (L := L) (Function.support H) hc
  let q := ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)
  have hq : q = ofBasis (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L) := by
    ext x z
    exact ofBasisMixed_norm_of_finite (b.baseChange L) x
      (AdelicStructure.forall_mem_Ωfin_algebraicExtension x) z
  have hm : ((q.restrict B).quotient U).IsMeasurable := by
    rw [hq]
    exact ofBasis_restrict_quotient_isMeasurable_of_all_finite
      (b.baseChange L) B U (hS := ⟨(AdelicStructure.forall_mem_Ωfin_algebraicExtension)⟩)
  apply isMeasurable_of_countable_localDist_zero _ _ (hθ := hm) _ ht
  intro x hx
  have hd := (((ξ.scalarExtension (L := L)).restrict B).localDist_quotient_le
    (q.restrict B) U x).trans
      (((ξ.scalarExtension (L := L)).localDist_restrict_le q B x).trans (hb L x))
  exact le_antisymm (hd.trans_eq (Function.notMem_support.mp hx))
    ((((ξ.scalarExtension (L := L)).restrict B).quotient U).localDist_nonneg
      ((q.restrict B).quotient U) x)

/-- The actual dual of every original-family native relative quotient is
measurable using the same produced countable scalar exception set. -/
theorem IsDominated.scalarExtension_restrict_quotient_dual_isMeasurable_of_pos_singletons
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E)
    (hξ : ξ.IsDominated) [hpos : S.HasPositiveSingletons]
    [hS : S.HasOnlyFinitePlaces]
    (B : Submodule L (L ⊗[K] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).dual.IsMeasurable := by
  let := AdelicStructure.measurableSingletonClass_algebraicExtension_of_finiteDimensional
    (S := S) (L := L)
  let b := Module.finBasis K E
  have hfin := AdelicStructure.v_Ωinf_lt_top_of_forall_mem_Ωfin (S := S)
  obtain ⟨H, _, _, hc, _, hb, _⟩ :=
    IsDominated.exists_scalarExtension_coordinate_exceptions_of_pos_singletons ξ b hξ hfin
  have ht := AdelicStructure.ParameterSpaceExtension.countable_preimage_proj_of_finiteDimensional
    (L := L) (Function.support H) hc
  let q := ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)
  have hq : q = ofBasis (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L) := by
    ext x z
    exact ofBasisMixed_norm_of_finite (b.baseChange L) x
      (AdelicStructure.forall_mem_Ωfin_algebraicExtension x) z
  have hm : ((q.restrict B).quotient U).dual.IsMeasurable := by
    rw [hq]
    exact ofBasis_restrict_quotient_dual_isMeasurable_of_all_finite
      (b.baseChange L) B U (hS := ⟨(AdelicStructure.forall_mem_Ωfin_algebraicExtension)⟩)
  apply isMeasurable_of_countable_localDist_zero _ _ (hθ := hm) _ ht
  intro x hx
  have hd := ((((ξ.scalarExtension (L := L)).restrict B).quotient U).localDist_dual_le
    ((q.restrict B).quotient U) x).trans
      ((((ξ.scalarExtension (L := L)).restrict B).localDist_quotient_le
        (q.restrict B) U x).trans
        (((ξ.scalarExtension (L := L)).localDist_restrict_le q B x).trans (hb L x)))
  exact le_antisymm (hd.trans_eq (Function.notMem_support.mp hx))
    ((((ξ.scalarExtension (L := L)).restrict B).quotient U).dual.localDist_nonneg
      ((q.restrict B).quotient U).dual x)

/-- Every dominated original family over the actual geometric projective line
has measurable native finite-extension subquotient norms, for any constant field. -/
theorem IsDominated.functionField_scalarExtension_restrict_quotient_isMeasurable
    {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] {E : Type*} [AddCommGroup E]
    [Module (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) (B : Submodule L (L ⊗[RatFunc k] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).IsMeasurable := by
  apply IsDominated.scalarExtension_restrict_quotient_isMeasurable_of_pos_singletons
    ξ hξ B U

/-- The same genuine projective-line regularity holds for actual native
subquotient duals, including zero spaces and equal relative endpoints. -/
theorem IsDominated.functionField_scalarExtension_restrict_quotient_dual_isMeasurable
    {k L : Type*} [Field k] [Field L] [Algebra (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] {E : Type*} [AddCommGroup E]
    [Module (RatFunc k) E] [FiniteDimensional (RatFunc k) E]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) (B : Submodule L (L ⊗[RatFunc k] E)) (U : Submodule L B) :
    (((ξ.scalarExtension (L := L)).restrict B).quotient U).dual.IsMeasurable := by
  apply IsDominated.scalarExtension_restrict_quotient_dual_isMeasurable_of_pos_singletons
    ξ hξ B U

end ArakelovGeometry.NormFamily

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Examples.FunctionFields
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Pointwise
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.AtomicNormComparison
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.PositiveAtoms.AtomicTail
import ArakelovGeometry.MeasureTheory.Measure.PositiveAtomic

/-!
# One countable base exceptional set for every actual algebraic extension

The pointwise scalar-extension distance envelope is integrable. Positive
singleton masses give countable actual support, so every extended completed
norm agrees with its coordinate family off one produced base set. Neither the
original norm nor the parameter space is assumed ultrametric or countable.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NormFamily

universe u w wE
variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ι : Type*} [Fintype ι]

/-- One produced countable base support works simultaneously for every
algebraic extension and every vector of its actual completed fibre. -/
theorem IsDominated.exists_scalarExtension_coordinate_exceptions_of_pos_singletons
    [MeasurableSingletonClass S.Ω] (ξ : NormFamily S E) (b : Module.Basis ι K E)
    (hξ : ξ.IsDominated) [hpos : S.HasPositiveSingletons]
    (hfin : S.v S.Ωinf < ⊤) :
    ∃ H : S.Ω → ℝ, Integrable H S.v ∧ (∀ ω, 0 ≤ H ω) ∧
      (Function.support H).Countable ∧
      (∀ ε : ℝ, 0 < ε → ∃ s : Finset S.Ω,
        (s : Set S.Ω) ⊆ Function.support H ∧
          (∫ ω in (s : Set S.Ω)ᶜ, |H ω| ∂S.v) < ε) ∧
      (∀ (L : Type w) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
        (x : S.ParameterSpaceExtension L),
        (ξ.scalarExtension (L := L)).localDist
          (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x ≤ H x.base) ∧
      ∀ (L : Type w) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
        (x : S.ParameterSpaceExtension L), x.base ∉ Function.support H →
        ∀ z : x.abv.Completion ⊗[L] (L ⊗[K] E),
          (ξ.scalarExtension (L := L)).norm x z =
            (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x z := by
  obtain ⟨H, hH, hH0, hb⟩ :=
    IsDominated.exists_scalarExtension_localDist_ofBasisMixed_pointwise_bound ξ b hξ hfin
  have hc := countable_support_of_integrable_of_pos_singletons hpos hH
  refine ⟨H, hH, hH0, hc, ?_, hb, ?_⟩
  · intro ε hε
    exact exists_finset_integral_abs_compl_lt_of_countable_support hH hc hε
  intro L _ _ _ x hx z
  have hd := hb L x
  rw [Function.notMem_support.mp hx] at hd
  have hz := le_antisymm hd
    ((ξ.scalarExtension (L := L)).localDist_nonneg
      (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x)
  have he := ((ξ.scalarExtension (L := L)).localDist_eq_zero_iff
    (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x).mp hz
  exact congrArg (fun n => n z) he

/-- Every original dominated family on the actual projective-line curve has
one countable base set controlling all its algebraic scalar extensions. -/
theorem IsDominated.functionField_scalarExtension_coordinate_exceptions
    {k : Type*} [Field k] {E : Type*} [AddCommGroup E] [Module (RatFunc k) E]
    [FiniteDimensional (RatFunc k) E] {ι : Type*} [Fintype ι]
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (b : Module.Basis ι (RatFunc k) E) (hξ : ξ.IsDominated) :
    ∃ H : (AdelicStructure.functionFieldAdelicStructure k).Ω → ℝ,
      Integrable H (AdelicStructure.functionFieldAdelicStructure k).v ∧
      (∀ ω, 0 ≤ H ω) ∧ (Function.support H).Countable ∧
      (∀ ε : ℝ, 0 < ε → ∃ s : Finset (AdelicStructure.functionFieldAdelicStructure k).Ω,
        (s : Set (AdelicStructure.functionFieldAdelicStructure k).Ω) ⊆ Function.support H ∧
          (∫ ω in (s : Set (AdelicStructure.functionFieldAdelicStructure k).Ω)ᶜ,
            |H ω| ∂(AdelicStructure.functionFieldAdelicStructure k).v) < ε) ∧
      (∀ (L : Type w) [Field L] [Algebra (RatFunc k) L] [Algebra.IsAlgebraic (RatFunc k) L]
        (x : (AdelicStructure.functionFieldAdelicStructure k).ParameterSpaceExtension L),
        (ξ.scalarExtension (L := L)).localDist
          (ofBasisMixed ((AdelicStructure.functionFieldAdelicStructure k).algebraicExtension L)
            (L ⊗[RatFunc k] E) (b.baseChange L)) x ≤ H x.base) ∧
      ∀ (L : Type w) [Field L] [Algebra (RatFunc k) L] [Algebra.IsAlgebraic (RatFunc k) L]
        (x : (AdelicStructure.functionFieldAdelicStructure k).ParameterSpaceExtension L),
        x.base ∉ Function.support H →
        ∀ z : x.abv.Completion ⊗[L] (L ⊗[RatFunc k] E),
          (ξ.scalarExtension (L := L)).norm x z =
            (ofBasisMixed ((AdelicStructure.functionFieldAdelicStructure k).algebraicExtension L)
              (L ⊗[RatFunc k] E) (b.baseChange L)).norm x z := by
  apply IsDominated.exists_scalarExtension_coordinate_exceptions_of_pos_singletons ξ b hξ
  rw [AdelicStructure.functionField_Ωinf_eq_empty, measure_empty]
  exact ENNReal.zero_lt_top

end ArakelovGeometry.NormFamily

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Minima.Basic
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
import ArakelovGeometry.AdelicVectorBundle.Minima.Basis
import ArakelovGeometry.AdelicVectorBundle.Minima.Restriction
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Actual line degree and rational vector degree

The actual rank-one determinant norm is normalized by its one-vector wedge.
This connects the determinant degree of a genuine rational line restriction
to its ambient vector degree, and proves the ordinary first-minimum bound by
maximal slope. Properness and the actual restriction/degree regularity
hypotheses remain explicit. No nonzero vector or line exists in rank zero.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

omit [FiniteDimensional K E] in
/-- In rank one the actual one-vector top wedge is nonzero precisely when
its rational generator is nonzero. -/
theorem determinant_single_wedge_ne_zero (hr : Module.finrank K E = 1)
    {s : E} (hs : s ≠ 0) :
    _root_.exteriorPower.ιMulti K (Module.finrank K E) (fun _ => s) ≠ 0 := by
  rw [hr]
  intro hz
  have h := congrArg (_root_.exteriorPower.oneEquiv K E) hz
  exact hs (by simpa only [_root_.exteriorPower.oneEquiv_ιMulti, map_zero] using h)

omit [FiniteDimensional K E] in
private theorem tensorToExterior_one_injective :
    Function.Injective (tensorToExterior K E 1) := by
  have he : (_root_.exteriorPower.oneEquiv K E).toLinearMap.comp (tensorToExterior K E 1) =
      (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => E) 0).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, tensorToExterior_tprod, _root_.exteriorPower.oneEquiv_ιMulti,
      PiTensorProduct.subsingletonEquiv_apply_tprod]
  intro x y h
  apply (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => E) 0).injective
  have hh := congrArg (_root_.exteriorPower.oneEquiv K E) h
  exact (DFunLike.congr_fun he x).symm.trans (hh.trans (DFunLike.congr_fun he y))

namespace NormFamily

/-- The actual rank-one determinant quotient is normalized by the one-vector
wedge at every completed place, including zero vectors and completed scalars. -/
theorem determinant_norm_single_wedge (ξ : NormFamily S E)
    (hr : Module.finrank K E = 1) (ω : S.Ω) (a : (S.ϕ ω).Completion) (s : E) :
    ξ.determinant.norm ω
      (a ⊗ₜ[K] _root_.exteriorPower.ιMulti K (Module.finrank K E) (fun _ => s)) =
      ξ.norm ω (a ⊗ₜ[K] s) := by
  change ((projectiveTensor (fun _ : Fin (Module.finrank K E) => ξ)).pushforward
    (tensorToExterior K E (Module.finrank K E))
      (tensorToExterior_surjective K E (Module.finrank K E))).norm ω _ = _
  rw [hr]
  rw [← tensorToExterior_tprod, ← LinearMap.baseChange_tmul,
    pushforward_norm_of_injective _ _ _ tensorToExterior_one_injective,
    projectiveTensor_norm_unique]
  simp only [tensorBaseChangeEquiv_tmul_tprod, map_smul,
    PiTensorProduct.subsingletonEquiv_apply_tprod, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

end NormFamily
namespace AdelicVectorBundle

variable [S.IsProper]

/-- The actual determinant degree of a line is the vector degree of every
nonzero rational generator, with no assumed determinant normalization. -/
theorem degree_eq_vectorDegree_of_finrank_one (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 1) (s : {x : E // x ≠ 0}) :
    V.degree hS hN = V.vectorDegree s := by
  rw [V.degree_eq_neg_integral hS hN
    ⟨_, determinant_single_wedge_ne_zero hr s.property⟩,
    vectorDegree, NormFamily.vectorDegree_eq_neg_integral]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω =>
    congrArg Real.log (V.toNormFamily.determinant_norm_single_wedge hr ω 1 s.val)

/-- The general determinant degree agrees with the existing line degree. -/
theorem degree_eq_lineDegree (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.IsLine) : V.degree hS hN = V.lineDegree hV := by
  rw [V.degree_eq_vectorDegree_of_finrank_one hS hN hV (V.lineGenerator hV),
    V.lineDegree_eq_vectorDegree hV (V.lineGenerator hV)]

/-- On an actual line every nonzero generator computes its first logarithmic
minimum and its line degree. Properness supplies generator independence. -/
theorem maximalLogarithmicMinimum_eq_lineDegree (V : AdelicVectorBundle S E)
    (hV : V.IsLine) : V.maximalLogarithmicMinimum = (V.lineDegree hV : EReal) := by
  let s := V.lineGenerator hV
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    obtain ⟨f, _, hf⟩ := (V.le_finrank_degreeThresholdSpan_iff 1 t).mp ht
    have he : V.vectorDegree (f 0) = V.lineDegree hV :=
      (V.lineDegree_eq_vectorDegree hV (f 0)).symm
    have h0 := hf 0
    rw [he] at h0
    exact EReal.coe_le_coe_iff.mpr h0
  · have hli : LinearIndependent K (fun _ : Fin 1 => s.val) :=
      linearIndependent_unique_iff.mpr s.property
    have h := V.coe_le_logarithmicMinimum_of_linearIndependent
      (fun _ : Fin 1 => s) hli (fun _ => le_rfl)
    change (V.lineDegree hV : EReal) ≤ V.logarithmicMinimum 1
    rw [V.lineDegree_eq_vectorDegree hV s]
    exact h

/-- The actual line degree of the canonical restriction to a nonzero vector's
span is its ambient vector degree. Rank zero is excluded by the vector domain. -/
theorem lineDegree_restrict_span_singleton (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (s : {x : E // x ≠ 0}) :
    (V.restrictOfMeasurableBase (K ∙ s.val) hS).lineDegree
      (finrank_span_singleton s.property) = V.vectorDegree s := by
  let u : {x : K ∙ s.val // x ≠ 0} :=
    ⟨⟨s.val, Submodule.mem_span_singleton_self s.val⟩, by
      intro h
      exact s.property (congrArg Subtype.val h)⟩
  rw [(V.restrictOfMeasurableBase (K ∙ s.val) hS).lineDegree_eq_vectorDegree
    (finrank_span_singleton s.property) u]
  exact V.vectorDegree_restrictOfMeasurableBase (K ∙ s.val) hS u

/-- The actual restricted-line determinant degree has the same vector value. -/
theorem degree_restrict_span_singleton (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (s : {x : E // x ≠ 0}) :
    (V.restrictOfMeasurableBase (K ∙ s.val) hS).degree hS hN = V.vectorDegree s := by
  rw [(V.restrictOfMeasurableBase (K ∙ s.val) hS).degree_eq_lineDegree hS hN
    (finrank_span_singleton s.property), V.lineDegree_restrict_span_singleton hS s]

/-- The genuine rank-one restricted slope equals ambient rational vector degree. -/
theorem slope_restrict_span_singleton (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (s : {x : E // x ≠ 0}) :
    (V.restrictOfMeasurableBase (K ∙ s.val) hS).slope hS hN = V.vectorDegree s := by
  rw [slope_eq_degree_of_finrank_one _ hS hN (finrank_span_singleton s.property),
    V.degree_restrict_span_singleton hS hN s]

/-- The ordinary first minimum is exactly the supremum of genuine restricted
line slopes, with an empty supremum in rank zero. -/
theorem maximalLogarithmicMinimum_eq_iSup_restrict_line_slopes (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.maximalLogarithmicMinimum =
      ⨆ (U : Submodule K E) (_ : Module.finrank K U = 1),
        ((V.restrictOfMeasurableBase U hS).slope hS hN : EReal) := by
  rw [V.maximalLogarithmicMinimum_eq_iSup_restrict_lines hS]
  apply iSup_congr
  intro U
  apply iSup_congr
  intro hU
  let R := V.restrictOfMeasurableBase U hS
  change R.logarithmicMinimum (Module.finrank K U) = (R.slope hS hN : EReal)
  rw [hU, R.slope_eq_degree_of_finrank_one hS hN hU, R.degree_eq_lineDegree hS hN hU]
  exact R.maximalLogarithmicMinimum_eq_lineDegree hU

/-- Every actual rational vector is bounded by the maximal slope through its
produced genuine restricted line. -/
theorem vectorDegree_le_maximalSlope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (s : {x : E // x ≠ 0}) : (V.vectorDegree s : EReal) ≤ V.maximalSlope hS hN := by
  rw [← V.slope_restrict_span_singleton hS hN s]
  apply V.slope_restrict_le_maximalSlope
  rw [finrank_span_singleton s.property]
  exact zero_lt_one

/-- The ordinary inequality of source Proposition 4.3.72, using actual line
slopes and the true maximal-slope supremum. Both zero values are bottom. -/
theorem maximalLogarithmicMinimum_le_maximalSlope (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.maximalLogarithmicMinimum ≤ V.maximalSlope hS hN := by
  rw [V.maximalLogarithmicMinimum_eq_iSup_restrict_line_slopes hS hN]
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  exact V.slope_restrict_le_maximalSlope U (by rw [hU]; exact zero_lt_one) hS hN

end AdelicVectorBundle
end ArakelovGeometry

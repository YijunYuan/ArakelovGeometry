/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Height.Basic
public import ArakelovGeometry.AdelicVectorBundle.Degree.Vector
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis

import ArakelovGeometry.AdelicCurve.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Coordinate heights as negative vector degrees

Source Remark 4.3.2 uses the actual coordinate-maximum norm, rather than the
mixed maximum/sum norm. Domination follows from their quantitative comparison.
The logarithmic height is the existing Chapter 3 height on rational tuples.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ι : Type wι} [Fintype ι]

/-- The completed coordinate-maximum family is dominated when infinity has finite measure.
The logarithmic rank correction is supported only on the Archimedean locus. -/
theorem ofBasis_isDominated_of_measure_lt_top (b : Module.Basis ι K E)
    (hfin : S.v S.Ωinf < ⊤) : (ofBasis S E b).IsDominated := by
  classical
  apply (ofBasisMixed_isDominated_of_measure_lt_top b hfin).of_localDist
  refine ⟨S.Ωinf.indicator (fun _ ↦ Real.log (Fintype.card ι : ℝ)),
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr (integrableOn_const hfin.ne), ?_⟩
  apply Eventually.of_forall
  intro ω
  rw [localDist_comm]
  exact ofBasis_localDist_ofBasisMixed_le b ω

/-- The source Archimedean normalization supplies the required finite measure. -/
theorem ofBasis_isDominated (b : Module.Basis ι K E)
    [hS : S.IsArchimedeanNormalized] :
    (ofBasis S E b).IsDominated :=
  ofBasis_isDominated_of_measure_lt_top b (S.v_Ωinf_lt_top_of_isRCLike)

variable [Nonempty ι]

/-- The canonical completed maximum norm evaluates to the source local height. -/
theorem ofBasisPi_norm_eq_localHeight (ω : S.Ω) (x : ι → K) :
    (ofBasis S (ι → K) (Pi.basisFun K ι)).norm ω
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) = S.localHeight x ω := by
  rw [ofBasis_norm_rational]
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply]
  have h0 : 0 ≤ S.localHeight x ω :=
    ((S.ϕ ω).nonneg (x (Classical.arbitrary ι))).trans
      (S.eval_le_localHeight x ω (Classical.arbitrary ι))
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg h0).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg ((S.ϕ ω).nonneg (x i))]
    exact S.eval_le_localHeight x ω i
  · apply Finset.sup'_le
    intro i _
    calc
      S.ϕ ω (x i) = ‖S.ϕ ω (x i)‖ :=
        (Real.norm_of_nonneg ((S.ϕ ω).nonneg (x i))).symm
      _ ≤ _ := norm_le_pi_norm (fun i ↦ S.ϕ ω (x i)) i

/-- Source Remark 4.3.2: coordinate height is the negative degree for the maximum norm.
For an empty coordinate type there is no nonzero vector, so this source assertion is empty. -/
theorem logHeight_eq_neg_vectorDegree (hfin : S.v S.Ωinf < ⊤)
    (s : {x : ι → K // x ≠ 0}) :
    S.logHeight s.val =
      -(ofBasis S (ι → K) (Pi.basisFun K ι)).vectorDegree
        (hd := (ofBasis_isDominated_of_measure_lt_top _ hfin))
            (hm := (ofBasis_isMeasurable _)) s := by
  rw [vectorDegree_eq_neg_integral, neg_neg]
  unfold AdelicStructure.logHeight
  apply integral_congr_ae
  exact Eventually.of_forall fun ω ↦ congrArg Real.log (ofBasisPi_norm_eq_localHeight ω s.val).symm

end ArakelovGeometry.NormFamily

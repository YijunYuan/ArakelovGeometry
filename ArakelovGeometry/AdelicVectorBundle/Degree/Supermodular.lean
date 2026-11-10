/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic
public import ArakelovGeometry.AdelicVectorBundle.Operator.Height
import ArakelovGeometry.AdelicVectorBundle.Degree.ExactSequence.Dual
import ArakelovGeometry.AdelicVectorBundle.Degree.Map
import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Functor
import ArakelovGeometry.MeasureTheory.Integral.UpperEnvelope
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Supermodularity of actual Hermitian degrees

The second isomorphism theorem is a contraction for the actual completed
quotient norms. Determinant contraction compares its degrees, and Hermitian
exact-sequence additivity gives supermodularity on the rational subspace lattice.
All statements include zero-dimensional intersections and quotients.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

namespace NormFamily

/-- The canonical second-isomorphism map contracts the actual completed
quotient norms. The proof compares every source lift, without choosing a
norm-minimizing lift. -/
theorem quotientInfEquivSupQuotient_norm_le [FiniteDimensional K E] (ξ : NormFamily S E)
    (U W : Submodule K E) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (U ⧸ (U.comap U.subtype ⊓ W.comap U.subtype))) :
    ((ξ.restrict (U ⊔ W)).quotient (W.comap (U ⊔ W).subtype)).norm ω
        ((LinearMap.quotientInfEquivSupQuotient U W).toLinearMap.baseChange
          (S.ϕ ω).Completion z) ≤
      ((ξ.restrict U).quotient (U.comap U.subtype ⊓ W.comap U.subtype)).norm ω z := by
  let I := U.comap U.subtype ⊓ W.comap U.subtype
  let J := W.comap (U ⊔ W).subtype
  let i := Submodule.inclusion (le_sup_left : U ≤ U ⊔ W)
  let e := LinearMap.quotientInfEquivSupQuotient U W
  have hc : e.toLinearMap.comp I.mkQ = J.mkQ.comp i := by
    ext x
    exact LinearMap.quotientInfEquivSupQuotient_apply_mk U W x
  have hs : (U ⊔ W).subtype.comp i = U.subtype := by
    ext x
    rfl
  apply ((ξ.restrict U).le_quotientSeminorm_iff I.mkQ I.mkQ_surjective ω z _).mpr
  intro x hx
  have he := DFunLike.congr_fun
    (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) hc) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at he
  rw [← hx, he]
  have hn := DFunLike.congr_fun
    (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) hs) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hn
  exact ((ξ.restrict (U ⊔ W)).quotient_norm_mk_le J ω
    (i.baseChange (S.ϕ ω).Completion x)).trans_eq
      (by simp only [restrict_norm]; rw [hn])

end NormFamily

namespace AdelicVectorBundle

variable [FiniteDimensional K E] [FiniteDimensional K F]

/-- A completed contraction has nonpositive actual lower-integral height,
including the zero map, whose height is `⊥`. -/
theorem mapHeight_le_zero_of_completed_contraction
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (f : E →ₗ[K] F)
    (hf : ∀ ω x, W.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ V.norm ω x) :
    V.mapHeight W f ≤ 0 := by
  by_cases hz : f = 0
  · subst f
    rw [V.mapHeight_zero W]
    exact bot_le
  rw [V.mapHeight_eq_lowerEnvelopeIntegral W hz]
  have h := lowerEnvelopeIntegral_mono (μ := S.v) (Eventually.of_forall
    (fun ω ↦ Real.log_nonpos (V.toNormFamily.operatorNorm_nonneg W.toNormFamily ω f)
      (V.toNormFamily.operatorNorm_le W.toNormFamily ω f (by norm_num)
        (by intro x; simpa only [one_mul] using hf ω x))))
  rw [lowerEnvelopeIntegral_eq_integral
    (show Integrable (fun _ : S.Ω ↦ (0 : ℝ)) S.v from integrable_zero S.Ω ℝ S.v),
    integral_zero, EReal.coe_zero] at h
  exact h

variable [S.IsProper]

/-- An equal-rank completed contraction compares actual real degrees.
The determinant argument also applies in rank zero. -/
theorem degree_le_of_completed_contraction
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F) (e : E ≃ₗ[K] F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (he : ∀ ω x, W.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) ≤ V.norm ω x) :
    V.degree hS hN ≤ W.degree hS hN := by
  have hd := determinantMap_ne_zero_of_injective e.toLinearMap e.finrank_eq e.injective
  have hl := lowerEnvelopeIntegral_mono (μ := S.v) (Eventually.of_forall
    (fun ω ↦ Real.log_nonpos
      (V.toNormFamily.determinant.operatorNorm_nonneg W.toNormFamily.determinant ω
        (determinantMap K e.toLinearMap e.finrank_eq))
      ((V.toNormFamily.determinantMap_operatorNorm_le_pow W.toNormFamily ω
        e.toLinearMap e.finrank_eq).trans
        (pow_le_one₀ (V.toNormFamily.operatorNorm_nonneg W.toNormFamily ω e.toLinearMap)
          (V.toNormFamily.operatorNorm_le W.toNormFamily ω e.toLinearMap (by norm_num)
            (by intro x; simpa only [one_mul] using he ω x))))))
  change lowerEnvelopeIntegral
    ((V.determinantOfMeasurableBase hS hN).toNormFamily.localHeight
      (W.determinantOfMeasurableBase hS hN).toNormFamily
      ⟨determinantMap K e.toLinearMap e.finrank_eq, hd⟩) S.v ≤ _ at hl
  rw [← (V.determinantOfMeasurableBase hS hN).mapHeight_eq_lowerEnvelopeIntegral
      (W.determinantOfMeasurableBase hS hN) hd,
    V.determinantMap_mapHeight_eq_degree_sub W hS hN e,
    lowerEnvelopeIntegral_eq_integral
      (show Integrable (fun _ : S.Ω ↦ (0 : ℝ)) S.v from integrable_zero S.Ω ℝ S.v),
    integral_zero] at hl
  exact sub_nonpos.mp (EReal.coe_le_coe_iff.mp hl)

/-- The actual quotient degrees in the second isomorphism theorem are ordered
in the direction induced by its completed contraction. -/
theorem degree_quotientInf_le_degree_supQuotient (V : AdelicVectorBundle S E)
    (U W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ((V.restrictOfMeasurableBase U hS).quotientOfMeasurableBase
      (U.comap U.subtype ⊓ W.comap U.subtype) hS).degree hS hN ≤
    ((V.restrictOfMeasurableBase (U ⊔ W) hS).quotientOfMeasurableBase
      (W.comap (U ⊔ W).subtype) hS).degree hS hN := by
  apply degree_le_of_completed_contraction _ _
    (LinearMap.quotientInfEquivSupQuotient U W) hS hN
  exact V.toNormFamily.quotientInfEquivSupQuotient_norm_le U W

/-- Actual Hermitian degree is supermodular on all rational subspaces. -/
theorem degree_restrict_inf_add_sup_ge_of_isHermitian (V : AdelicVectorBundle S E)
    (U W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    (V.restrictOfMeasurableBase U hS).degree hS hN +
      (V.restrictOfMeasurableBase W hS).degree hS hN ≤
    (V.restrictOfMeasurableBase (U ⊓ W) hS).degree hS hN +
      (V.restrictOfMeasurableBase (U ⊔ W) hS).degree hS hN := by
  have hc := V.degree_quotientInf_le_degree_supQuotient U W hS hN
  have hU := (V.restrictOfMeasurableBase U hS).degree_restrict_add_degree_quotient_eq_of_isHermitian
      ((U ⊓ W).comap U.subtype) hS hN (hV.restrict U)
  have hUW := degree_restrict_add_degree_quotient_eq_of_isHermitian
    (V.restrictOfMeasurableBase (U ⊔ W) hS)
    (W.comap (U ⊔ W).subtype) hS hN (hV.restrict (U ⊔ W))
  rw [V.degree_restrict_restrict (U ⊓ W) U inf_le_left hS hN] at hU
  rw [V.degree_restrict_restrict W (U ⊔ W) le_sup_right hS hN] at hUW
  rw [Submodule.comap_inf] at hU
  linarith

end AdelicVectorBundle

end ArakelovGeometry

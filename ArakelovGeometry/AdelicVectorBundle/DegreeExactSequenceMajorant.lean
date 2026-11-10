/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.DegreeExactSequence
import ArakelovGeometry.AdelicVectorBundle.DiscrepancyExactSequence

/-!
# The exact-sequence degree bound by global majorant discrepancy

The actual determinant operator bound gives a pointwise logarithmic
inequality. Translation and superadditivity of lower integrals then prove
the degree comparison, including infinite global discrepancies.
-/

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

/-- The intrinsic majorant-infimum bound controls the actual compatible
determinant log norms, with no original ultrametricity assumption. -/
theorem determinantSequence_log_majorantDiscrepancy_le (ξ : NormFamily S E)
    (W : Submodule K E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {z : ⋀[K]^(Module.finrank K W) W}
    {q : ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)}
    (hz : z ≠ 0) (hq : q ≠ 0) (ω : S.Ω) :
    Real.log ((ξ.restrict W).majorantDiscrepancy hN ω) +
        Real.log ((ξ.quotient W).majorantDiscrepancy hN ω) ≤
      Real.log (ξ.majorantDiscrepancy hN ω) +
        ξ.determinant.logNorm (determinantSequenceEquiv W (z ⊗ₜ[K] q)) ω -
        (ξ.restrict W).determinant.logNorm z ω -
        (ξ.quotient W).determinant.logNorm q ω := by
  let DW := ⋀[K]^(Module.finrank K W) W
  let DQ := ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)
  let D := (ξ.restrict W).determinant.injectiveTensorPair (ξ.quotient W).determinant
  have hrW : Module.finrank K DW = 1 := determinant_finrank
  have hrQ : Module.finrank K DQ = 1 := determinant_finrank
  have hr : Module.finrank K (DW ⊗[K] DQ) = 1 := by
    rw [Module.finrank_tensorProduct, hrW, hrQ, mul_one]
  have hpW := (ξ.restrict W).determinant.norm_rational_pos ω hz
  have hpQ := (ξ.quotient W).determinant.norm_rational_pos ω hq
  have hn := (ξ.restrict W).determinant.injectiveTensorPair_norm_rational_generators
    (ξ.quotient W).determinant hrW hrQ hz hq ω
  have ht : z ⊗ₜ[K] q ≠ 0 := by
    intro h
    rw [h, TensorProduct.tmul_zero, D.norm_zero] at hn
    linarith [mul_pos hpW hpQ]
  have he : determinantSequenceEquiv W (z ⊗ₜ[K] q) ≠ 0 := by
    intro h
    apply ht
    exact (determinantSequenceEquiv W).injective (h.trans (map_zero _).symm)
  have hpE := ξ.determinant.norm_rational_pos ω he
  have hΔW := (ξ.restrict W).majorantDiscrepancy_pos hN ω
  have hΔQ := (ξ.quotient W).majorantDiscrepancy_pos hN ω
  have hΔE := ξ.majorantDiscrepancy_pos hN ω
  have h := Real.log_le_log (div_pos (mul_pos hΔW hΔQ) hΔE)
    (ξ.majorantDiscrepancy_restrict_mul_quotient_div_le_operatorNorm hN W ω)
  rw [D.operatorNorm_eq_div_of_finrank_one ξ.determinant hr
    (determinantSequenceEquiv W).toLinearMap ht ω, hn] at h
  change Real.log ((ξ.restrict W).majorantDiscrepancy hN ω *
      (ξ.quotient W).majorantDiscrepancy hN ω / ξ.majorantDiscrepancy hN ω) ≤
    Real.log (ξ.determinant.norm ω (1 ⊗ₜ[K] determinantSequenceEquiv W (z ⊗ₜ[K] q)) /
      ((ξ.restrict W).determinant.norm ω (1 ⊗ₜ[K] z) *
        (ξ.quotient W).determinant.norm ω (1 ⊗ₜ[K] q))) at h
  rw [Real.log_div (mul_pos hΔW hΔQ).ne' hΔE.ne',
    Real.log_mul hΔW.ne' hΔQ.ne',
    Real.log_div hpE.ne' (mul_pos hpW hpQ).ne',
    Real.log_mul hpW.ne' hpQ.ne'] at h
  simp only [logNorm]
  linarith

end NormFamily

namespace AdelicVectorBundle

/-- Translating by the actual integrable determinant log norms proves the
two-step capital-discrepancy degree estimate without subtracting infinities. -/
theorem degree_add_majorantDiscrepancy_restrict_add_quotient_le [S.IsProper]
    (V : AdelicVectorBundle S E) (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.degree hS hN : EReal) +
        (V.restrictOfMeasurableBase W hS).majorantDiscrepancy hN +
        (V.quotientOfMeasurableBase W hS).majorantDiscrepancy hN ≤
      ((V.restrictOfMeasurableBase W hS).degree hS hN : EReal) +
        ((V.quotientOfMeasurableBase W hS).degree hS hN : EReal) +
        V.majorantDiscrepancy hN := by
  let z : {z : ⋀[K]^(Module.finrank K W) W // z ≠ 0} :=
    ⟨determinantGenerator, determinantGenerator_ne_zero⟩
  let q : {q : ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W) // q ≠ 0} :=
    ⟨determinantGenerator, determinantGenerator_ne_zero⟩
  let e := determinantSequenceEquiv W (z.val ⊗ₜ[K] q.val)
  have he : e ≠ 0 := by
    let DW := ⋀[K]^(Module.finrank K W) W
    let DQ := ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)
    let x : ∀ i, BinaryTensorFactors DW DQ i := fun i ↦ match i with
      | .inl _ => z.val
      | .inr _ => q.val
    have hr : ∀ i, Module.finrank K (BinaryTensorFactors DW DQ i) = 1 := by
      rintro (i | i) <;> exact NormFamily.determinant_finrank
    have hx : ∀ i, x i ≠ 0 := by
      rintro (i | i)
      · exact z.property
      · exact q.property
    have ht := NormFamily.tensor_generators_ne_zero hr x hx
    intro h
    apply ht
    apply (binaryTensorEquiv K (BinaryTensorFactors DW DQ)).injective
    have h' : z.val ⊗ₜ[K] q.val = 0 :=
      (determinantSequenceEquiv W).injective
        (h.trans (determinantSequenceEquiv W).map_zero.symm)
    simpa only [binaryTensorEquiv_tprod, map_zero] using h'
  let f := fun ω ↦ Real.log ((V.toNormFamily.restrict W).majorantDiscrepancy hN ω)
  let g := fun ω ↦ Real.log ((V.toNormFamily.quotient W).majorantDiscrepancy hN ω)
  let d := fun ω ↦ Real.log (V.toNormFamily.majorantDiscrepancy hN ω)
  let a := V.toNormFamily.determinant.logNorm e -
    (V.toNormFamily.restrict W).determinant.logNorm z.val -
    (V.toNormFamily.quotient W).determinant.logNorm q.val
  have iz : Integrable ((V.toNormFamily.restrict W).determinant.logNorm z.val) S.v := by
    simpa only [determinantOfMeasurableBase_toNormFamily,
      restrictOfMeasurableBase_toNormFamily] using
      ((V.restrictOfMeasurableBase W hS).determinantOfMeasurableBase hS hN).integrable_logNorm
        z.val
  have iq : Integrable ((V.toNormFamily.quotient W).determinant.logNorm q.val) S.v := by
    simpa only [determinantOfMeasurableBase_toNormFamily,
      quotientOfMeasurableBase_toNormFamily] using
      ((V.quotientOfMeasurableBase W hS).determinantOfMeasurableBase hS hN).integrable_logNorm
        q.val
  have ie : Integrable (V.toNormFamily.determinant.logNorm e) S.v := by
    simpa only [determinantOfMeasurableBase_toNormFamily] using
      (V.determinantOfMeasurableBase hS hN).integrable_logNorm e
  have ia : Integrable a S.v := (ie.sub iz).sub iq
  have hfg : f + g ≤ᵐ[S.v] d + a := by
    apply Filter.Eventually.of_forall
    intro ω
    simpa only [f, g, d, a, Pi.add_apply, Pi.sub_apply, add_sub, sub_add_eq_add_sub] using
      V.toNormFamily.determinantSequence_log_majorantDiscrepancy_le W hN
        z.property q.property ω
  have hi := (lowerEnvelopeIntegral_add_le (μ := S.v) f g).trans
    (lowerEnvelopeIntegral_mono hfg)
  rw [lowerEnvelopeIntegral_add_integrable d ia] at hi
  have hR := V.degree_restrict_eq_neg_integral W hS hN z
  have hQ := V.degree_quotient_eq_neg_integral W hS hN q
  have hE := V.degree_eq_neg_integral hS hN ⟨e, he⟩
  have ha : (∫ ω, a ω ∂S.v) =
      (V.restrictOfMeasurableBase W hS).degree hS hN +
        (V.quotientOfMeasurableBase W hS).degree hS hN - V.degree hS hN := by
    have hsub := integral_sub (ie.sub iz) iq
    have hsub' := integral_sub ie iz
    change (∫ ω, a ω ∂S.v) =
      (∫ ω, (V.toNormFamily.determinant.logNorm e -
        (V.toNormFamily.restrict W).determinant.logNorm z.val) ω ∂S.v) -
        (∫ ω, (V.toNormFamily.quotient W).determinant.logNorm q.val ω ∂S.v) at hsub
    rw [hsub]
    change (∫ ω, (V.toNormFamily.determinant.logNorm e -
        (V.toNormFamily.restrict W).determinant.logNorm z.val) ω ∂S.v) =
      (∫ ω, V.toNormFamily.determinant.logNorm e ω ∂S.v) -
        (∫ ω, (V.toNormFamily.restrict W).determinant.logNorm z.val ω ∂S.v) at hsub'
    rw [hsub']
    linarith
  rw [ha] at hi
  change (V.restrictOfMeasurableBase W hS).majorantDiscrepancy hN +
      (V.quotientOfMeasurableBase W hS).majorantDiscrepancy hN ≤
    V.majorantDiscrepancy hN +
      ((V.restrictOfMeasurableBase W hS).degree hS hN +
        (V.quotientOfMeasurableBase W hS).degree hS hN - V.degree hS hN : ℝ) at hi
  have h := add_le_add_right hi (V.degree hS hN : EReal)
  calc
    _ = ((V.restrictOfMeasurableBase W hS).majorantDiscrepancy hN +
        (V.quotientOfMeasurableBase W hS).majorantDiscrepancy hN) +
        (V.degree hS hN : EReal) := by ac_rfl
    _ ≤ (V.majorantDiscrepancy hN +
        ((V.restrictOfMeasurableBase W hS).degree hS hN +
          (V.quotientOfMeasurableBase W hS).degree hS hN - V.degree hS hN : ℝ)) +
        (V.degree hS hN : EReal) := by convert h using 1 <;> ac_rfl
    _ = V.majorantDiscrepancy hN +
        ((V.restrictOfMeasurableBase W hS).degree hS hN +
          (V.quotientOfMeasurableBase W hS).degree hS hN : ℝ) := by
      rw [add_assoc, ← EReal.coe_add, sub_add_cancel]
    _ = _ := by rw [EReal.coe_add]; ac_rfl

/-- The source subtraction form of the two-step capital degree bound.
The infinite middle discrepancy is handled first; otherwise the genuine
end discrepancies are finite by their already proved global bounds. -/
theorem degree_sub_majorantDiscrepancy_le_restrict_add_quotient [S.IsProper]
    (V : AdelicVectorBundle S E) (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.degree hS hN : EReal) - V.majorantDiscrepancy hN ≤
      (((V.restrictOfMeasurableBase W hS).degree hS hN : EReal) -
        (V.restrictOfMeasurableBase W hS).majorantDiscrepancy hN) +
      (((V.quotientOfMeasurableBase W hS).degree hS hN : EReal) -
        (V.quotientOfMeasurableBase W hS).majorantDiscrepancy hN) := by
  by_cases hE : V.majorantDiscrepancy hN = ⊤
  · rw [hE, EReal.sub_top]
    exact bot_le
  · have hR : (V.restrictOfMeasurableBase W hS).majorantDiscrepancy hN ≠ ⊤ :=
      ne_of_lt ((V.majorantDiscrepancy_restrict_le W hS hN).trans_lt
        (lt_top_iff_ne_top.mpr hE))
    have hQ : (V.quotientOfMeasurableBase W hS).majorantDiscrepancy hN ≠ ⊤ :=
      ne_of_lt ((V.majorantDiscrepancy_quotient_le W hS hN).trans_lt
        (lt_top_iff_ne_top.mpr hE))
    have hi := V.degree_add_majorantDiscrepancy_restrict_add_quotient_le W hS hN
    lift V.majorantDiscrepancy hN to ℝ using
      ⟨hE, (V.bot_lt_majorantDiscrepancy hN).ne'⟩ with d hd
    lift (V.restrictOfMeasurableBase W hS).majorantDiscrepancy hN to ℝ using
      ⟨hR, ((V.restrictOfMeasurableBase W hS).bot_lt_majorantDiscrepancy hN).ne'⟩ with r hr
    lift (V.quotientOfMeasurableBase W hS).majorantDiscrepancy hN to ℝ using
      ⟨hQ, ((V.quotientOfMeasurableBase W hS).bot_lt_majorantDiscrepancy hN).ne'⟩ with q hq
    simp only [← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff] at hi ⊢
    linarith

end AdelicVectorBundle

end ArakelovGeometry

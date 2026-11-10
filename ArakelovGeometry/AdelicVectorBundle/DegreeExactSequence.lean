/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree
public import ArakelovGeometry.AdelicVectorBundle.DeterminantDiscrepancy
public import ArakelovGeometry.AdelicVectorBundle.DeterminantSequenceOperator

/-!
# The lower degree bound in an exact sequence

The canonical determinant contraction is integrated on the actual restriction
and quotient adelic bundles. No auxiliary determinant norm or integrability
certificate is assumed. Empty subspaces and zero quotients are included.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

private theorem determinantSequence_tmul_ne_zero (W : Submodule K E)
    {z : ⋀[K]^(Module.finrank K W) W}
    {q : ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)}
    (hz : z ≠ 0) (hq : q ≠ 0) : determinantSequenceEquiv W (z ⊗ₜ[K] q) ≠ 0 := by
  let DW := ⋀[K]^(Module.finrank K W) W
  let DQ := ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)
  let x : ∀ i, BinaryTensorFactors DW DQ i := fun i ↦ match i with
    | .inl _ => z
    | .inr _ => q
  have hr : ∀ i, Module.finrank K (BinaryTensorFactors DW DQ i) = 1 := by
    rintro (i | i)
    · exact NormFamily.determinant_finrank
    · exact NormFamily.determinant_finrank
  have hx : ∀ i, x i ≠ 0 := by
    rintro (i | i)
    · exact hz
    · exact hq
  have ht := NormFamily.tensor_generators_ne_zero hr x hx
  intro he
  have he' : z ⊗ₜ[K] q = 0 := (determinantSequenceEquiv W).injective
    (he.trans (determinantSequenceEquiv W).map_zero.symm)
  apply ht
  apply (binaryTensorEquiv K (BinaryTensorFactors DW DQ)).injective
  simpa only [binaryTensorEquiv_tprod, map_zero] using he'

namespace NormFamily

/-- The actual exact-sequence determinant map contracts rational log norms. -/
theorem determinantSequence_logNorm_tmul_le (ξ : NormFamily S E) (W : Submodule K E)
    {z : ⋀[K]^(Module.finrank K W) W}
    {q : ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)}
    (hz : z ≠ 0) (hq : q ≠ 0) (ω : S.Ω) :
    ξ.determinant.logNorm (determinantSequenceEquiv W (z ⊗ₜ[K] q)) ω ≤
      (ξ.restrict W).determinant.logNorm z ω +
        (ξ.quotient W).determinant.logNorm q ω := by
  have hz' := (ξ.restrict W).determinant.norm_rational_pos ω hz
  have hq' := (ξ.quotient W).determinant.norm_rational_pos ω hq
  have h := Real.log_le_log
    (ξ.determinant.norm_rational_pos ω (determinantSequence_tmul_ne_zero W hz hq))
    (ξ.determinantSequence_norm_rational_tmul_le W ω z q)
  simpa only [logNorm, Real.log_mul (ne_of_gt hz') (ne_of_gt hq')] using h

end NormFamily

namespace AdelicVectorBundle

/-- Integrating the actual determinant contraction gives the log-integral
comparison for a two-step exact sequence. -/
theorem integral_determinantSequence_logNorm_le (V : AdelicVectorBundle S E)
    (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {z : ⋀[K]^(Module.finrank K W) W}
    {q : ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)}
    (hz : z ≠ 0) (hq : q ≠ 0) :
    (∫ ω, V.toNormFamily.determinant.logNorm
      (determinantSequenceEquiv W (z ⊗ₜ[K] q)) ω ∂S.v) ≤
      (∫ ω, (V.toNormFamily.restrict W).determinant.logNorm z ω ∂S.v) +
        (∫ ω, (V.toNormFamily.quotient W).determinant.logNorm q ω ∂S.v) := by
  have iz : Integrable ((V.toNormFamily.restrict W).determinant.logNorm z) S.v := by
    simpa only [determinantOfMeasurableBase_toNormFamily,
      restrictOfMeasurableBase_toNormFamily] using
      ((V.restrictOfMeasurableBase W hS).determinantOfMeasurableBase hS hN).integrable_logNorm z
  have iq : Integrable ((V.toNormFamily.quotient W).determinant.logNorm q) S.v := by
    simpa only [determinantOfMeasurableBase_toNormFamily,
      quotientOfMeasurableBase_toNormFamily] using
      ((V.quotientOfMeasurableBase W hS).determinantOfMeasurableBase hS hN).integrable_logNorm q
  have ie : Integrable (V.toNormFamily.determinant.logNorm
      (determinantSequenceEquiv W (z ⊗ₜ[K] q))) S.v := by
    simpa only [determinantOfMeasurableBase_toNormFamily] using
      (V.determinantOfMeasurableBase hS hN).integrable_logNorm
        (determinantSequenceEquiv W (z ⊗ₜ[K] q))
  have h := integral_mono ie (iz.add iq)
    (fun ω ↦ V.toNormFamily.determinantSequence_logNorm_tmul_le W hz hq ω)
  change (∫ ω, V.toNormFamily.determinant.logNorm
      (determinantSequenceEquiv W (z ⊗ₜ[K] q)) ω ∂S.v) ≤
    (∫ ω, (V.toNormFamily.restrict W).determinant.logNorm z ω +
      (V.toNormFamily.quotient W).determinant.logNorm q ω ∂S.v) at h
  rwa [integral_add iz iq] at h

/-- A nonzero determinant vector computes the restricted bundle degree
using exactly the actual restricted norm family. -/
theorem degree_restrict_eq_neg_integral [S.IsProper] (V : AdelicVectorBundle S E)
    (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (z : {z : ⋀[K]^(Module.finrank K W) W // z ≠ 0}) :
    (V.restrictOfMeasurableBase W hS).degree hS hN =
      -(∫ ω, (V.toNormFamily.restrict W).determinant.logNorm z.val ω ∂S.v) := by
  simpa only [restrictOfMeasurableBase_toNormFamily] using
    (V.restrictOfMeasurableBase W hS).degree_eq_neg_integral hS hN z

/-- A nonzero determinant vector computes the quotient bundle degree
using exactly the actual quotient norm family. -/
theorem degree_quotient_eq_neg_integral [S.IsProper] (V : AdelicVectorBundle S E)
    (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (q : {q : ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W) // q ≠ 0}) :
    (V.quotientOfMeasurableBase W hS).degree hS hN =
      -(∫ ω, (V.toNormFamily.quotient W).determinant.logNorm q.val ω ∂S.v) := by
  simpa only [quotientOfMeasurableBase_toNormFamily] using
    (V.quotientOfMeasurableBase W hS).degree_eq_neg_integral hS hN q

/-- Degrees are superadditive for the actual restricted and quotient bundles,
the two-step lower inequality of Proposition 4.3.13. -/
theorem degree_restrict_add_degree_quotient_le [S.IsProper] (V : AdelicVectorBundle S E)
    (W : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (V.restrictOfMeasurableBase W hS).degree hS hN +
        (V.quotientOfMeasurableBase W hS).degree hS hN ≤ V.degree hS hN := by
  let z : {z : ⋀[K]^(Module.finrank K W) W // z ≠ 0} :=
    ⟨determinantGenerator, determinantGenerator_ne_zero⟩
  let q : {q : ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W) // q ≠ 0} :=
    ⟨determinantGenerator, determinantGenerator_ne_zero⟩
  let e := determinantSequenceEquiv W (z.val ⊗ₜ[K] q.val)
  have he : e ≠ 0 := determinantSequence_tmul_ne_zero W z.property q.property
  have hR := V.degree_restrict_eq_neg_integral W hS hN z
  have hQ := V.degree_quotient_eq_neg_integral W hS hN q
  have hE := V.degree_eq_neg_integral hS hN ⟨e, he⟩
  have h := V.integral_determinantSequence_logNorm_le W hS hN z.property q.property
  calc
    _ = -(∫ ω, (V.toNormFamily.restrict W).determinant.logNorm z.val ω ∂S.v) +
        -(∫ ω, (V.toNormFamily.quotient W).determinant.logNorm q.val ω ∂S.v) :=
      congrArg₂ (fun a b : ℝ ↦ a + b) hR hQ
    _ = -((∫ ω, (V.toNormFamily.restrict W).determinant.logNorm z.val ω ∂S.v) +
        (∫ ω, (V.toNormFamily.quotient W).determinant.logNorm q.val ω ∂S.v)) :=
      (neg_add _ _).symm
    _ ≤ -(∫ ω, V.toNormFamily.determinant.logNorm e ω ∂S.v) := neg_le_neg h
    _ = V.degree hS hN := hE.symm


end AdelicVectorBundle

end ArakelovGeometry

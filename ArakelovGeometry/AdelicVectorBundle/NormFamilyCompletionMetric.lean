/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.NormFamilyMetricEnvelope
import ArakelovGeometry.AdelicVectorBundle.StrongSubquotient
import Mathlib.Topology.MetricSpace.Gluing

/-!
# The metric of strongly dominated norm families

The first assertion of Chen–Moriwaki, Remark 4.1.20: the upper integral
of actual local logarithmic distance is a finite pseudometric, whose
separation quotient identifies exactly almost-everywhere equal fibre norms.
Finite measure of the infinite locus is explicit; the source's usual
Archimedean normalization implies this hypothesis. No measurability of
norm families is imposed. Completeness is a separate result.
-/

open MeasureTheory Filter

namespace ArakelovGeometry

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

namespace NormFamily

/-- The extended upper integral of the actual local logarithmic distance.
It is finite on strongly dominated pairs when the infinite locus has finite measure. -/
noncomputable def upperIntegralDist (ξ η : NormFamily S E) : EReal :=
  upperEnvelopeIntegral (ξ.localDist η) S.v

theorem upperIntegralDist_nonneg (ξ η : NormFamily S E) :
    0 ≤ ξ.upperIntegralDist η :=
  upperEnvelopeIntegral_nonneg (Eventually.of_forall (ξ.localDist_nonneg η))

theorem upperIntegralDist_ne_bot (ξ η : NormFamily S E) :
    ξ.upperIntegralDist η ≠ ⊥ :=
  ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (ξ.upperIntegralDist_nonneg η))

theorem upperIntegralDist_lt_top {ξ η : NormFamily S E}
    (hξ : ξ.IsStronglyDominated) (hη : η.IsStronglyDominated)
    (hfin : S.v S.Ωinf < ⊤) : ξ.upperIntegralDist η < ⊤ :=
  hasIntegrableUpperBound_iff_upperEnvelopeIntegral_lt_top.mp
    (hξ.localDist hη hfin).1

/-- The standing usual-absolute-value hypothesis of Chapter 4 supplies finite
measure of the infinite locus, hence finiteness of the source distance. -/
theorem upperIntegralDist_lt_top_of_isRCLike {ξ η : NormFamily S E}
    (hξ : ξ.IsStronglyDominated) (hη : η.IsStronglyDominated)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ξ.upperIntegralDist η < ⊤ :=
  upperIntegralDist_lt_top hξ hη (S.v_Ωinf_lt_top_of_isRCLike hS)

@[simp]
theorem upperIntegralDist_self (ξ : NormFamily S E) : ξ.upperIntegralDist ξ = 0 := by
  unfold upperIntegralDist
  have he : ξ.localDist ξ = 0 := funext ξ.localDist_self
  rw [he, upperEnvelopeIntegral_eq_integral (integrable_zero _ _ _)]
  simp

omit [FiniteDimensional K E] in
theorem upperIntegralDist_comm (ξ η : NormFamily S E) :
    ξ.upperIntegralDist η = η.upperIntegralDist ξ := by
  unfold upperIntegralDist
  congr 1
  funext ω
  exact ξ.localDist_comm η ω

theorem upperIntegralDist_triangle (ξ η ζ : NormFamily S E) :
    ξ.upperIntegralDist ζ ≤ ξ.upperIntegralDist η + η.upperIntegralDist ζ := by
  exact (upperEnvelopeIntegral_mono
    (Eventually.of_forall (ξ.localDist_triangle η ζ))).trans
      (upperEnvelopeIntegral_add_le
        (Eventually.of_forall (ξ.localDist_nonneg η))
        (Eventually.of_forall (η.localDist_nonneg ζ)))

/-- Zero upper-integral distance detects equality of entire fibre norms on one
common conull set, not merely separate almost-everywhere evaluation equalities. -/
theorem upperIntegralDist_eq_zero_iff (ξ η : NormFamily S E) :
    ξ.upperIntegralDist η = 0 ↔ ∀ᵐ ω ∂S.v, ξ.norm ω = η.norm ω := by
  rw [upperIntegralDist,
    upperEnvelopeIntegral_eq_zero_iff (Eventually.of_forall (ξ.localDist_nonneg η))]
  exact eventually_congr (Eventually.of_forall (ξ.localDist_eq_zero_iff η))

omit [FiniteDimensional K E] in
/-- Simultaneously changing both fibre norms on null sets leaves distance unchanged. -/
theorem upperIntegralDist_congr {ξ ξ' η η' : NormFamily S E}
    (hξ : ∀ᵐ ω ∂S.v, ξ.norm ω = ξ'.norm ω)
    (hη : ∀ᵐ ω ∂S.v, η.norm ω = η'.norm ω) :
    ξ.upperIntegralDist η = ξ'.upperIntegralDist η' := by
  apply upperEnvelopeIntegral_congr
  filter_upwards [hξ, hη] with ω hξω hηω
  simp only [localDist, hξω, hηω]

end NormFamily

/-- The actual strongly dominated norm families on a finite-dimensional vector space. -/
abbrev StronglyDominatedNormFamily (S : AdelicStructure.{u, v} K) (E : Type w)
    [AddCommGroup E] [Module K E] [FiniteDimensional K E] :=
  {ξ : NormFamily S E // ξ.IsStronglyDominated}

namespace StronglyDominatedNormFamily

variable [Fact (S.v S.Ωinf < ⊤)]

/-- The source upper-integral pseudometric on strongly dominated norm families. -/
noncomputable instance instPseudoMetricSpace :
    PseudoMetricSpace (StronglyDominatedNormFamily S E) where
  dist ξ η := (ξ.val.upperIntegralDist η.val).toReal
  dist_self ξ := by simp
  dist_comm ξ η := by rw [ξ.val.upperIntegralDist_comm η.val]
  dist_triangle ξ η ζ := by
    have h := EReal.toReal_le_toReal (ξ.val.upperIntegralDist_triangle η.val ζ.val)
      (ξ.val.upperIntegralDist_ne_bot ζ.val)
      (EReal.add_ne_top
        (NormFamily.upperIntegralDist_lt_top ξ.property η.property Fact.out).ne
        (NormFamily.upperIntegralDist_lt_top η.property ζ.property Fact.out).ne)
    rwa [EReal.toReal_add
      (NormFamily.upperIntegralDist_lt_top ξ.property η.property Fact.out).ne
      (ξ.val.upperIntegralDist_ne_bot η.val)
      (NormFamily.upperIntegralDist_lt_top η.property ζ.property Fact.out).ne
      (η.val.upperIntegralDist_ne_bot ζ.val)] at h

theorem dist_eq_upperIntegralDist (ξ η : StronglyDominatedNormFamily S E) :
    (dist ξ η : EReal) = ξ.val.upperIntegralDist η.val :=
  EReal.coe_toReal
    (NormFamily.upperIntegralDist_lt_top ξ.property η.property Fact.out).ne
    (ξ.val.upperIntegralDist_ne_bot η.val)

/-- The pseudometric separates exactly the almost-everywhere classes of fibre norms. -/
theorem dist_eq_zero_iff (ξ η : StronglyDominatedNormFamily S E) :
    dist ξ η = 0 ↔ ∀ᵐ ω ∂S.v, ξ.val.norm ω = η.val.norm ω := by
  rw [← ξ.val.upperIntegralDist_eq_zero_iff η.val, ← dist_eq_upperIntegralDist]
  exact EReal.coe_eq_zero.symm

/-- The canonical metric quotient by almost-everywhere equality of actual fibres. -/
abbrev AEQuotient (S : AdelicStructure.{u, v} K) (E : Type w)
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [Fact (S.v S.Ωinf < ⊤)] :=
  SeparationQuotient (StronglyDominatedNormFamily S E)

/-- The canonical separation quotient identifies precisely the source equivalence relation. -/
theorem quotient_mk_eq_mk_iff (ξ η : StronglyDominatedNormFamily S E) :
    SeparationQuotient.mk ξ = SeparationQuotient.mk η ↔
      ∀ᵐ ω ∂S.v, ξ.val.norm ω = η.val.norm ω := by
  rw [← _root_.dist_eq_zero, SeparationQuotient.dist_mk, dist_eq_zero_iff]

/-- The quotient metric retains the upper integral of the original local distance. -/
theorem quotient_dist_eq_upperIntegralDist (ξ η : StronglyDominatedNormFamily S E) :
    (dist (SeparationQuotient.mk ξ) (SeparationQuotient.mk η) : EReal) =
      ξ.val.upperIntegralDist η.val := by
  rw [SeparationQuotient.dist_mk, dist_eq_upperIntegralDist]

end StronglyDominatedNormFamily

end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.NormFamilyCompletionDensity
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldFullLatticeGauge
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldNormalizationHermitian

/-!
# Classical number-field norm families and their density

The corrected strongly dominated form of Chen–Moriwaki, Remark 4.1.36.
Classicality uses actual full integral lattices and their literal completed
scalar-infimum gauges. It does not require arbitrary exceptional finite
norms to be ultrametric. The printed assertion for merely dominated families
is not asserted.
-/

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped NumberField TensorProduct
noncomputable section

namespace ArakelovGeometry

open AdelicStructure ActualPrimeIndexing NumberFieldFullLattice
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

private abbrev N := normalizedNumberFieldAdelicStructure K

namespace NormFamily

/-- Literal completed gauges of one full finite integral lattice, with finite exceptions.
The model is automatically finite projective over the ring of integers. -/
def IsClassical (ξ : NormFamily (N (K := K)) E) : Prop :=
  ∃ L : Submodule (𝓞 K) E, L.FG ∧ Submodule.span K (L : Set E) = ⊤ ∧
    ∃ T : Set (N (K := K)).Ω, T.Finite ∧ ∀ p : HeightOneSpectrum (𝓞 K),
      normalizedPrimeParameter p ∉ T → ∀ z,
      ξ.norm (normalizedPrimeParameter p) z =
        scalarLatticeGauge (F := ((N (K := K)).ϕ (normalizedPrimeParameter p)).Completion)
          (NumberFieldModel.completedLatticeSpan L p : Set _) z

omit [FiniteDimensional K E] in
/-- A literal full-lattice family is classical with no exceptional finite primes. -/
theorem isClassical_fullLatticeGaugeFamily (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (N (K := K)) E) :
    (fullLatticeGaugeFamily L hfg hspan η).IsClassical :=
  ⟨L, hfg, hspan, ∅, Set.finite_empty, fun p _ z ↦
    fullLatticeGaugeFamily_norm_prime L hfg hspan η p z⟩

/-- The full model's produced domination and ultrametricity give strong domination. -/
theorem fullLatticeGaugeFamily_isStronglyDominated
    (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (η : NormFamily (N (K := K)) E) :
    (fullLatticeGaugeFamily L hfg hspan η).IsStronglyDominated :=
  ((fullLatticeGaugeFamily L hfg hspan η).isStronglyDominated_iff_isDominated_of_ultrametric
    (fullLatticeGaugeFamily_isUltrametric L hfg hspan η)
    normalizedNumberFieldArchimedeanCompletions).mpr
      (fullLatticeGaugeFamily_coherent_and_dominated L hfg hspan η).2

/-- Classical families are strongly dominated even with nonultrametric exceptional norms. -/
theorem IsClassical.isStronglyDominated {ξ : NormFamily (N (K := K)) E}
    (hξ : ξ.IsClassical) : ξ.IsStronglyDominated := by
  obtain ⟨L, hfg, hspan, T, hT, heq⟩ := hξ
  let η := fullLatticeGaugeFamily L hfg hspan ξ
  apply (fullLatticeGaugeFamily_isStronglyDominated L hfg hspan ξ).of_localDist
  refine ⟨η.localDist ξ, integrable_localDist_of_norm_eq_off_finite η ξ
    (T ∪ (N (K := K)).Ωinf) (hT.union normalizedInfiniteLocus_finite) ?_,
    Eventually.of_forall fun _ ↦ le_rfl⟩
  intro ω hω z
  have hfin : ω ∈ (N (K := K)).Ωfin := by
    by_contra h
    exact hω (Or.inr h)
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hfin
  rw [fullLatticeGaugeFamily_norm_prime]
  exact (heq p (fun hp ↦ hω (Or.inl hp)) z).symm

omit [FiniteDimensional K E] in
/-- Finite changes preserve the literal common-lattice model. -/
theorem IsClassical.of_norm_eq_off_finite {ξ η : NormFamily (N (K := K)) E}
    (hη : η.IsClassical) (T : Set (N (K := K)).Ω) (hT : T.Finite)
    (heq : ∀ ω ∉ T, ξ.norm ω = η.norm ω) : ξ.IsClassical := by
  obtain ⟨L, hfg, hspan, F, hF, hmodel⟩ := hη
  refine ⟨L, hfg, hspan, T ∪ F, hT.union hF, fun p hp z ↦ ?_⟩
  rw [heq _ (fun h ↦ hp (Or.inl h))]
  exact hmodel p (fun h ↦ hp (Or.inr h)) z

/-- A finite basis produces an actual full integral lattice and hence a classical family. -/
theorem exists_isClassical : ∃ ξ : NormFamily (N (K := K)) E, ξ.IsClassical := by
  let b := Module.finBasis K E
  let L : Submodule (𝓞 K) E := Submodule.span (𝓞 K) (Set.range b)
  have hfg : L.FG := Submodule.fg_span (Set.finite_range b)
  have hspan : Submodule.span K (L : Set E) = ⊤ := by
    apply top_le_iff.mp
    rw [← b.span_eq]
    apply Submodule.span_mono
    exact Submodule.subset_span
  let η := ofBasisMixed (N (K := K)) E b
  exact ⟨fullLatticeGaugeFamily L hfg hspan η,
    isClassical_fullLatticeGaugeFamily L hfg hspan η⟩

end NormFamily

namespace StronglyDominatedNormFamily

private instance normalizedInfiniteMeasureFinite :
    Fact ((N (K := K)).v (N (K := K)).Ωinf < ⊤) :=
  ⟨(N (K := K)).v_Ωinf_lt_top_of_isRCLike normalizedNumberFieldArchimedeanCompletions⟩

private instance normalizedPlacesCountable : Countable (N (K := K)).Ω :=
  inferInstanceAs (Countable {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})

private instance normalizedMeasurableSingletons : MeasurableSingletonClass (N (K := K)).Ω :=
  inferInstanceAs (MeasurableSingletonClass
    {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})

/-- On the countable discrete number-field place space the distance is the ordinary integral. -/
theorem numberField_dist_eq_integral
    (ξ η : StronglyDominatedNormFamily (N (K := K)) E) :
    dist ξ η = ∫ ω, ξ.val.localDist η.val ω ∂(N (K := K)).v := by
  have hi : Integrable (ξ.val.localDist η.val) (N (K := K)).v :=
    (ξ.property.localDist η.property Fact.out).integrable
      (measurable_of_countable _).aestronglyMeasurable
  apply EReal.coe_injective
  rw [dist_eq_upperIntegralDist]
  exact upperEnvelopeIntegral_eq_integral hi

/-- Actual classical lattice families are dense in the strongly dominated domain. -/
theorem dense_isClassical :
    Dense {ξ : StronglyDominatedNormFamily (N (K := K)) E | ξ.val.IsClassical} := by
  obtain ⟨η, hη⟩ := NormFamily.exists_isClassical (K := K) (E := E)
  let η' : StronglyDominatedNormFamily (N (K := K)) E := ⟨η, hη.isStronglyDominated⟩
  apply (dense_finite_modifications η').mono
  intro ξ hξ
  obtain ⟨T, hT, heq⟩ := hξ
  exact hη.of_norm_eq_off_finite T hT heq

/-- Positive mass of every number-field place makes the source distance separate actual families. -/
theorem numberField_eq_of_dist_eq_zero
    (ξ η : StronglyDominatedNormFamily (N (K := K)) E) (h : dist ξ η = 0) : ξ = η := by
  apply Subtype.ext
  apply NormFamily.ext
  intro ω z
  have he := ae_iff_of_countable.mp ((dist_eq_zero_iff ξ η).mp h) ω
    (normalized_singleton_pos ω).ne'
  exact congrArg (fun p ↦ p z) he

/-- The already constructed source pseudometric is a metric over the normalized number field. -/
theorem numberFieldT0Space : T0Space (StronglyDominatedNormFamily (N (K := K)) E) :=
  (t0Space_iff_inseparable _).mpr fun ξ η h ↦
    numberField_eq_of_dist_eq_zero ξ η h.dist_eq_zero

/-- The metric strengthening retains the original upper-integral distance and topology. -/
@[instance_reducible]
noncomputable def numberFieldMetricSpace :
    MetricSpace (StronglyDominatedNormFamily (N (K := K)) E) := by
  letI := numberFieldT0Space (K := K) (E := E)
  exact MetricSpace.ofT0PseudoMetricSpace _

/-- Classical families, as the actual classical subspace of strongly dominated families. -/
abbrev ClassicalFamily (K : Type*) [Field K] [NumberField K]
    (E : Type*) [AddCommGroup E] [Module K E] [FiniteDimensional K E] :=
  {ξ : StronglyDominatedNormFamily (normalizedNumberFieldAdelicStructure K) E //
    ξ.val.IsClassical}

/-- The canonical inclusion is an isometry for the source upper-integral metric. -/
theorem classicalFamily_isometry :
    Isometry (Subtype.val : ClassicalFamily K E →
      StronglyDominatedNormFamily (N (K := K)) E) := isometry_subtype_coe

/-- The strongly dominated space is an actual completion of its classical lattice subspace. -/
noncomputable def classicalFamilyCompletion : AbstractCompletion (ClassicalFamily K E) where
  space := StronglyDominatedNormFamily (N (K := K)) E
  coe := Subtype.val
  uniformStruct := inferInstance
  complete := inferInstance
  separation := numberFieldT0Space
  isUniformInducing := classicalFamily_isometry.isUniformInducing
  dense := by
    intro ξ
    apply closure_mono (s := {ζ : StronglyDominatedNormFamily (N (K := K)) E |
      ζ.val.IsClassical}) ?_ (dense_isClassical ξ)
    intro ζ hζ
    exact ⟨⟨ζ, hζ⟩, rfl⟩

end StronglyDominatedNormFamily
end ArakelovGeometry

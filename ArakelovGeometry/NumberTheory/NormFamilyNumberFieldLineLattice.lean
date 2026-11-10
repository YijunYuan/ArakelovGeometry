/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNormalizedCompletedCoherence
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldLatticeGauge
import ArakelovGeometry.NumberTheory.NumberFieldBoundedIndexElement
import ArakelovGeometry.AdelicVectorBundle.Restriction

/-!
# Actual restricted line lattices

The literal completed restriction gives the intersection of the global
integral ball with each actual subspace. Genuine coherence and domination
produce spanning and finite generation; in dimension one this produces
invertibility and an actual bounded-index element.
-/

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Pointwise

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing CompletedUnitBallGauge

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]

variable (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)

theorem restrict_rationalUnitBall_eq_preimage (F : Submodule K E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω) :
    (ξ.restrict F).rationalUnitBall ω = F.subtype ⁻¹' ξ.rationalUnitBall ω := by
  ext x
  rfl

theorem restrict_globalUnitBall_eq_preimage (F : Submodule K E) :
    (ξ.restrict F).globalUnitBall = F.subtype ⁻¹' ξ.globalUnitBall := by
  ext x
  rfl

theorem restrict_globalUnitBallModule_eq_comap (hξ : ξ.IsUltrametric)
    (F : Submodule K E) :
    (ξ.restrict F).globalUnitBallModule (hξ.restrict F) =
      (ξ.globalUnitBallModule hξ).comap (F.subtype.restrictScalars (𝓞 K)) := by
  ext x
  rfl

theorem restrict_completedUnitBallModule_eq_comap (hξ : ξ.IsUltrametric)
    (F : Submodule K E) (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    (ξ.restrict F).completedUnitBallModule ω hω (hξ.restrict F) =
      (ξ.completedUnitBallModule ω hω hξ).comap
        (LinearMap.restrictScalars
          ((normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω)
          (F.subtype.baseChange ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion)) := by
  ext x
  rfl

/-- The scalar-infimum gauges of the literal completed balls restrict exactly. -/
theorem completedUnitBallGauge_restrict (F : Submodule K E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] F) :
    completedUnitBallGauge (ξ.restrict F) ω z = completedUnitBallGauge ξ ω
      (F.subtype.baseChange ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion z) := by
  unfold completedUnitBallGauge scalarLatticeGauge scalarLatticeGaugeValues
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  constructor <;> rintro ⟨a, ha, hball, har⟩
  · refine ⟨a, ha, ?_, har⟩
    change ξ.norm ω (a⁻¹ • _) ≤ 1
    change (ξ.restrict F).norm ω (a⁻¹ • z) ≤ 1 at hball
    simpa only [restrict_norm, map_smul] using hball
  · refine ⟨a, ha, ?_, har⟩
    change (ξ.restrict F).norm ω (a⁻¹ • z) ≤ 1
    change ξ.norm ω (a⁻¹ • _) ≤ 1 at hball
    simpa only [restrict_norm, map_smul] using hball

theorem HasFiniteNormExceptions.restrict
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hfinite : ξ.HasFiniteNormExceptions) (F : Submodule K E) :
    (ξ.restrict F).HasFiniteNormExceptions := by
  intro x
  simpa only [restrict_norm_tmul] using hfinite (x : E)

/-- The literal inclusion of the actual restricted integral lattice. -/
def restrictedGlobalUnitBallInclusion (hξ : ξ.IsUltrametric) (F : Submodule K E) :
    (ξ.restrict F).globalUnitBallModule (hξ.restrict F) →ₗ[𝓞 K]
      ξ.globalUnitBallModule hξ where
  toFun x := ⟨(x.val : E), x.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem restrictedGlobalUnitBallInclusion_coe (hξ : ξ.IsUltrametric) (F : Submodule K E)
    (x : (ξ.restrict F).globalUnitBallModule (hξ.restrict F)) :
    (ξ.restrictedGlobalUnitBallInclusion hξ F x : E) = (x.val : E) := rfl

theorem restrictedGlobalUnitBallInclusion_injective (hξ : ξ.IsUltrametric)
    (F : Submodule K E) : Function.Injective (ξ.restrictedGlobalUnitBallInclusion hξ F) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ξ.globalUnitBallModule hξ => (z : E)) h

variable [FiniteDimensional K E]

theorem latticeGaugeFamily_restrict (hξ : ξ.IsUltrametric) (F : Submodule K E) :
    (ξ.restrict F).latticeGaugeFamily (hξ.restrict F) = (ξ.latticeGaugeFamily hξ).restrict F := by
  ext ω z
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · rw [(ξ.restrict F).latticeGaugeFamily_norm_finite (hξ.restrict F) ω hω,
      restrict_norm, ξ.latticeGaugeFamily_norm_finite hξ ω hω,
      ξ.completedUnitBallGauge_restrict F ω z]
  · rw [(ξ.restrict F).latticeGaugeFamily_norm_not_finite (hξ.restrict F) ω hω]
    simp only [restrict_norm, ξ.latticeGaugeFamily_norm_not_finite hξ ω hω]

theorem IsDominated.fg_restrict_normalizedGlobalUnitBallModule
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hdom : ξ.IsDominated) (hξ : ξ.IsUltrametric) (F : Submodule K E) :
    ((ξ.restrict F).globalUnitBallModule (hξ.restrict F)).FG := by
  let : Module.Finite (𝓞 K) (ξ.globalUnitBallModule hξ) :=
    Module.Finite.iff_fg.mpr (hdom.fg_normalizedGlobalUnitBallModule hξ)
  have hfinite : Module.Finite (𝓞 K)
      ((ξ.restrict F).globalUnitBallModule (hξ.restrict F)) :=
    Module.Finite.of_injective (ξ.restrictedGlobalUnitBallInclusion hξ F)
      (ξ.restrictedGlobalUnitBallInclusion_injective hξ F)
  exact Module.Finite.iff_fg.mp hfinite

omit [FiniteDimensional K E] in
theorem HasFiniteNormExceptions.span_restrict_normalizedGlobalUnitBall_eq_top
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hfinite : ξ.HasFiniteNormExceptions) (F : Submodule K E) :
    Submodule.span K (ξ.restrict F).globalUnitBall = ⊤ :=
  (hfinite.restrict F).span_globalUnitBall_eq_top (fun ω _ =>
    NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω))

theorem HasFiniteNormExceptions.restricted_normalizedGlobalCompletedTensorMap_bijective
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hfinite : ξ.HasFiniteNormExceptions) (hξ : ξ.IsUltrametric)
    (F : Submodule K E) (p : HeightOneSpectrum (𝓞 K)) :
    Function.Bijective ((ξ.restrict F).normalizedGlobalUnitBallCompletedTensorMap
      (hξ.restrict F) p) :=
  (hfinite.restrict F).normalizedGlobalUnitBallCompletedTensorMap_bijective (hξ.restrict F) p

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NumberFieldLineLattice

variable {K F : Type*} [Field K] [NumberField K] [AddCommGroup F] [Module K F]

/-- A full finite integral lattice in an actual one-dimensional number-field
space is invertible; the fractional-ideal realization is produced. -/
theorem invertible_of_fg_of_span_eq_top_of_finrank_eq_one
    (L : Submodule (𝓞 K) F) (hL : L.FG)
    (hspan : Submodule.span K (L : Set F) = ⊤) (hrank : Module.finrank K F = 1) :
    Module.Invertible (𝓞 K) L := by
  let : Module (𝓞 K) K := (inferInstance : Algebra (𝓞 K) K).toModule
  let : FaithfulSMul (𝓞 K) K := inferInstance
  let e : K ≃ₗ[K] F := (Module.nonempty_linearEquiv_of_finrank_eq_one hrank).some
  let f : F →ₗ[𝓞 K] K := e.symm.toLinearMap.restrictScalars (𝓞 K)
  have hf : Function.Injective f := e.symm.injective
  let J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ⟨L.map f, FractionalIdeal.isFractional_of_fg (hL.map f)⟩
  have hLne : L ≠ ⊥ := by
    let : Nontrivial F := Module.nontrivial_of_finrank_pos (by rw [hrank]; norm_num)
    intro h
    simp [h] at hspan
  have hJne : J ≠ 0 := by
    intro h
    have hmap : L.map f = ⊥ := FractionalIdeal.coeToSubmodule_eq_bot.mpr h
    have hzero := congrArg (Submodule.comap f) hmap
    rw [Submodule.comap_map_eq_of_injective hf, Submodule.comap_bot,
      LinearMap.ker_eq_bot.mpr hf] at hzero
    exact hLne hzero
  have hmul : (J : Submodule (𝓞 K) K) *
      ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) = 1 := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJne,
      FractionalIdeal.coe_one]
  let U : (Submodule (𝓞 K) K)ˣ :=
    ⟨J, ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K),
      hmul, by simpa only [mul_comm] using hmul⟩
  let : Module.Invertible (𝓞 K) (L.map f) :=
    Module.Invertible.left (Submodule.tensorInvEquiv U)
  exact Module.Invertible.congr (Submodule.equivMapOfInjective f hf L).symm

end ArakelovGeometry.NumberFieldLineLattice

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

theorem normalizedLineGlobalUnitBall_invertible
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsUltrametric) (hfinite : ξ.HasFiniteNormExceptions) (hdom : ξ.IsDominated)
    (F : Submodule K E) (hrank : Module.finrank K F = 1) :
    Module.Invertible (𝓞 K) ((ξ.restrict F).globalUnitBallModule (hξ.restrict F)) :=
  NumberFieldLineLattice.invertible_of_fg_of_span_eq_top_of_finrank_eq_one _
    (hdom.fg_restrict_normalizedGlobalUnitBallModule hξ F)
    (hfinite.span_restrict_normalizedGlobalUnitBall_eq_top F) hrank

theorem exists_normalizedLineGlobalUnitBall_boundedIndex_element
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsUltrametric) (hfinite : ξ.HasFiniteNormExceptions) (hdom : ξ.IsDominated)
    (F : Submodule K E) (hrank : Module.finrank K F = 1) :
    ∃ l : (ξ.restrict F).globalUnitBallModule (hξ.restrict F), l ≠ 0 ∧
      Finite (((ξ.restrict F).globalUnitBallModule (hξ.restrict F)) ⧸
        Submodule.span (𝓞 K) {l}) ∧
      Nat.card (((ξ.restrict F).globalUnitBallModule (hξ.restrict F)) ⧸
        Submodule.span (𝓞 K) {l}) ≤ NumberFieldBoundedIndex.indexBound K := by
  let := ξ.normalizedLineGlobalUnitBall_invertible hξ hfinite hdom F hrank
  exact NumberFieldBoundedIndex.exists_invertibleModule_boundedIndex_element K
    ((ξ.restrict F).globalUnitBallModule (hξ.restrict F))

end ArakelovGeometry.NormFamily

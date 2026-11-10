/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyCompletedLocalLattice
import ArakelovGeometry.NumberTheory.CompletedUnitBallGaugeComparison
import ArakelovGeometry.AdelicVectorBundle.BasisNorm
import ArakelovGeometry.AdelicVectorBundle.Comparison

/-!
# The actual number-field lattice-gauge norm family

Replace finite norms by the intrinsic gauges of their literal completed
unit balls, and retain the original norms at infinity. The produced local
unit-ball basis supplies separating norms without a gauge-norm certificate.
The canonical local distance is the actual local impurity. No global
coherence, domination or impurity summability is asserted here.
-/

open scoped NumberField TensorProduct

noncomputable section

attribute [local instance] Classical.propDecidable

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing CompletedUnitBallGauge

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The produced completed-ball basis generates exactly the rational basis
lattice in the original actual completed fibre. -/
theorem completedUnitBallModule_eq_completedBasisLattice
    {S : AdelicStructure K} (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) (hξ : ξ.IsUltrametric) :
    ξ.completedUnitBallModule ω hω hξ = completedBasisLattice S
      (ξ.rationalLocalUnitBallGenericBasis ω hω hnt hξ) ω hω := by
  let N := ξ.completedUnitBallModule ω hω hξ
  let b := ξ.completedUnitBallBasis ω hω hnt hξ
  have hs := congrArg (Submodule.map N.subtype) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hs
  dsimp only [N] at hs
  rw [completedBasisLattice_eq_span, ← hs]
  apply congrArg (Submodule.span (S.completedLocalRing ω hω))
  rw [← Set.range_comp]
  apply congrArg Set.range
  funext i
  change (ξ.completedUnitBallBasis ω hω hnt hξ i : (S.ϕ ω).Completion ⊗[K] E) = _
  rw [ξ.completedUnitBallBasis_coe, ξ.rationalLocalUnitBallGenericBasis_coe]

/-- The intrinsic scalar infimum of the actual completed ball is its produced
local rational basis norm. -/
theorem completedUnitBallGauge_eq_basisNorm
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (hnt : ((normalizedNumberFieldAdelicStructure K).ϕ ω).IsNontrivial)
    (hξ : ξ.IsUltrametric)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E) :
    completedUnitBallGauge ξ ω z =
      (ofBasis (normalizedNumberFieldAdelicStructure K) E
        (ξ.rationalLocalUnitBallGenericBasis ω hω hnt hξ)).norm ω z := by
  unfold completedUnitBallGauge
  rw [← ξ.coe_completedUnitBallModule ω hω hξ,
    ξ.completedUnitBallModule_eq_completedBasisLattice ω hω hnt hξ]
  exact scalarLatticeGauge_completedBasisLattice _ ω hω hnt z

variable (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
  (hξ : ξ.IsUltrametric)

/-- Finite completed ball gauges and original infinite norms on the same
actual normalized number-field fibres. -/
def latticeGaugeFamily : NormFamily (normalizedNumberFieldAdelicStructure K) E where
  norm ω := if hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin then
    (ofBasis (normalizedNumberFieldAdelicStructure K) E
      (ξ.rationalLocalUnitBallGenericBasis ω hω
        (NormalizedNumberFieldPlaces.parameter_isNontrivial
          (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)) hξ)).norm ω
    else ξ.norm ω
  norm_eq_zero_iff ω z := by
    split
    · exact (ofBasis _ E _).norm_eq_zero_iff ω z
    · exact ξ.norm_eq_zero_iff ω z

theorem latticeGaugeFamily_norm_finite
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E) :
    (ξ.latticeGaugeFamily hξ).norm ω z = completedUnitBallGauge ξ ω z := by
  dsimp only [latticeGaugeFamily]
  rw [dif_pos hω]
  exact (ξ.completedUnitBallGauge_eq_basisNorm ω hω _ hξ z).symm

theorem latticeGaugeFamily_norm_not_finite
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∉ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    (ξ.latticeGaugeFamily hξ).norm ω = ξ.norm ω := by
  change (if hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin then _ else _) = _
  rw [dif_neg hω]

theorem latticeGaugeFamily_isUltrametric : (ξ.latticeGaugeFamily hξ).IsUltrametric := by
  intro ω hω x y
  let b := ξ.rationalLocalUnitBallGenericBasis ω hω
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)) hξ
  have hn : ∀ z, (ξ.latticeGaugeFamily hξ).norm ω z =
      (ofBasisMixed (normalizedNumberFieldAdelicStructure K) E b).norm ω z := by
    intro z
    rw [ofBasisMixed_norm_of_finite b ω hω]
    dsimp only [latticeGaugeFamily]
    rw [dif_pos hω]
  simp only [hn]
  exact ofBasisMixed_isUltrametric b ω hω x y

theorem latticeGaugeFamily_completedUnitBall_eq
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    (ξ.latticeGaugeFamily hξ).completedUnitBall ω = ξ.completedUnitBall ω := by
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  ext z
  change (ξ.latticeGaugeFamily hξ).norm _ z ≤ 1 ↔ _
  rw [ξ.latticeGaugeFamily_norm_finite hξ _ (normalizedPrimeParameter_mem_fin p)]
  exact completedUnitBallGauge_le_one_iff ξ p z

theorem latticeGaugeFamily_rationalUnitBall_eq
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    (ξ.latticeGaugeFamily hξ).rationalUnitBall ω = ξ.rationalUnitBall ω := by
  ext x
  change (1 ⊗ₜ[K] x) ∈ (ξ.latticeGaugeFamily hξ).completedUnitBall ω ↔
    (1 ⊗ₜ[K] x) ∈ ξ.completedUnitBall ω
  rw [ξ.latticeGaugeFamily_completedUnitBall_eq hξ ω hω]

theorem latticeGaugeFamily_globalUnitBall_eq :
    (ξ.latticeGaugeFamily hξ).globalUnitBall = ξ.globalUnitBall := by
  ext x
  simp only [mem_globalUnitBall]
  constructor <;> intro hx ω hω
  · rw [← ξ.latticeGaugeFamily_rationalUnitBall_eq hξ ω hω]
    exact hx ω hω
  · rw [ξ.latticeGaugeFamily_rationalUnitBall_eq hξ ω hω]
    exact hx ω hω

theorem latticeGaugeFamily_globalUnitBallModule_eq :
    (ξ.latticeGaugeFamily hξ).globalUnitBallModule
      (ξ.latticeGaugeFamily_isUltrametric hξ) = ξ.globalUnitBallModule hξ := by
  ext x
  change x ∈ (ξ.latticeGaugeFamily hξ).globalUnitBall ↔ x ∈ ξ.globalUnitBall
  rw [ξ.latticeGaugeFamily_globalUnitBall_eq hξ]

/-- The canonical completed-fibre distance equals the actual source local
impurity, including the zero-dimensional convention. -/
theorem latticeGaugeFamily_localDist_finite
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    ξ.localDist (ξ.latticeGaugeFamily hξ) ω = completedUnitBallImpurity ξ ω := by
  obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
  let ω := normalizedPrimeParameter p
  have hf := normalizedPrimeParameter_mem_fin p
  have hlog (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E)
      (hz : z ≠ 0) :
      |Real.log (ξ.norm ω z) - Real.log ((ξ.latticeGaugeFamily hξ).norm ω z)| =
        Real.log (completedUnitBallGauge ξ ω z / ξ.norm ω z) := by
    have hp := ξ.norm_pos ω hz
    have hq := (ξ.latticeGaugeFamily hξ).norm_pos ω hz
    have hle := (completedUnitBallGauge_comparison ξ p z).1
    rw [ξ.latticeGaugeFamily_norm_finite hξ ω hf] at hq ⊢
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hp hle)),
      neg_sub, Real.log_div hq.ne' hp.ne']
  rw [ξ.localDist_eq_sSup]
  unfold completedUnitBallImpurity
  congr 1
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (hlog z hz).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, hlog z hz⟩

theorem latticeGaugeFamily_localDist_not_finite
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∉ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    ξ.localDist (ξ.latticeGaugeFamily hξ) ω = 0 := by
  apply (ξ.localDist_eq_zero_iff _ ω).mpr
  exact (ξ.latticeGaugeFamily_norm_not_finite hξ ω hω).symm

end ArakelovGeometry.NormFamily

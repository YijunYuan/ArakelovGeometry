/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Line.FullLatticeIndex
public import ArakelovGeometry.NumberTheory.NumberField.Model.Sections

import ArakelovGeometry.AdelicCurve.Equiv
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry
import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.HNSections
import Mathlib.Topology.Sheaves.Init

/-! # The literal original arithmetic model of a pure restricted Hermitian bundle -/

@[expose] public section

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldClassicalRestrictionModel

open AdelicStructure NumberFieldFullLattice NumberFieldProjectiveGeneric
open NumberFieldInvertibleGeneric (genericInclusion genericImage genericImage_fullSpan)

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K))
  [hV : V.toNormFamily.IsHermitian]
  [hpure : V.toNormFamily.IsPureAtFinitePlaces]

include hpure in
/-- The actual finite global ball is a finite original arithmetic module. -/
theorem integralModel_finite :
    Module.Finite (𝓞 K) (V.toNormFamily.globalUnitBallModule (hξ := hV.1)) :=
  Module.Finite.of_fg
    (V.isDominated.pure_normalizedGlobalUnitBall_finite_projective_span hV.1 hpure).1

include hpure in
/-- The actual finite global ball is projective over the original integer ring. -/
theorem integralModel_projective :
    Module.Projective (𝓞 K) (V.toNormFamily.globalUnitBallModule (hξ := hV.1)) :=
  (V.isDominated.pure_normalizedGlobalUnitBall_finite_projective_span hV.1 hpure).2.1

/-- Canonical scalar extension of the literal finite global lattice, with its
actual inclusion into the rational space. -/
def integralModelGenericEquiv :
    K ⊗[𝓞 K] (V.toNormFamily.globalUnitBallModule (hξ := hV.1)) ≃ₗ[K] V :=
  genericTensorEquiv _
    (V.isDominated.pure_normalizedGlobalUnitBall_finite_projective_span hV.1 hpure).2.2

@[simp]
theorem integralModelGenericEquiv_original
    (m : V.toNormFamily.globalUnitBallModule (hξ := hV.1)) :
    integralModelGenericEquiv V
      (genericInclusion (K := K) (V.toNormFamily.globalUnitBallModule
          (hξ := hV.1)) m) = (m : V) := by
  change genericTensorEquiv _ _ ((1 : K) ⊗ₜ[𝓞 K] m) = _
  erw [genericTensorEquiv_tmul, one_smul]

/-- The actual original arithmetic norms pulled back from the pure bundle. -/
def integralModelFamily :
    NormFamily (normalizedNumberFieldAdelicStructure K)
      (K ⊗[𝓞 K] (V.toNormFamily.globalUnitBallModule (hξ := hV.1))) :=
  V.toNormFamily.pullback (integralModelGenericEquiv V).toLinearMap
    (integralModelGenericEquiv V).injective

/-- The actual generic pullback retains the prescribed Hermitian norms. -/
theorem integralModelFamily_isHermitian :
    (integralModelFamily V).IsHermitian
      :=
  hV.pullback _ _

/-- Its literal finite global ball is precisely the original generic image. -/
theorem integralModelFamily_globalUnitBallModule :
    (integralModelFamily V).globalUnitBallModule
      (hξ := (integralModelFamily_isHermitian V).1) =
      genericImage (K := K) (V.toNormFamily.globalUnitBallModule (hξ := hV.1)) := by
  let L := V.toNormFamily.globalUnitBallModule (hξ := hV.1)
  let e := integralModelGenericEquiv V
  have hmem (x : K ⊗[𝓞 K] L) :
      x ∈ (integralModelFamily V).globalUnitBall ↔ e x ∈ L := by
    change (∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin,
      (integralModelFamily V).norm ω (1 ⊗ₜ[K] x) ≤ 1) ↔
      ∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin,
        V.toNormFamily.norm ω (1 ⊗ₜ[K] e x) ≤ 1
    rfl
  ext x
  constructor
  · intro hx
    have hxL := (hmem x).mp hx
    refine ⟨⟨e x, hxL⟩, ?_⟩
    apply e.injective
    exact integralModelGenericEquiv_original V ⟨e x, hxL⟩
  · rintro ⟨m, rfl⟩
    apply (hmem _).mpr
    rw [integralModelGenericEquiv_original]
    exact m.property

/-- The canonical original arithmetic finite gauges are the actual pulled-back
finite norms; the equality also retains all prescribed infinite norms. -/
theorem integralModelFamily_eq_fullLatticeGaugeFamily :
    letI := integralModel_finite V
    fullLatticeGaugeFamily
      (genericImage (K := K) (V.toNormFamily.globalUnitBallModule (hξ := hV.1)))
      (genericImage_fg _) (genericImage_fullSpan _)
      (integralModelFamily V) = integralModelFamily V := by
  let := integralModel_finite V
  let e := integralModelGenericEquiv V
  let η := integralModelFamily V
  have hd : η.IsDominated := V.isDominated.pullback e.toLinearMap e.injective
  have hp : η.IsPureAtFinitePlaces := hpure.pullback e.toLinearMap e.injective
  obtain ⟨hfg, hspan, he⟩ := hd.exists_pure_fullLatticeGaugeFamily_eq
    (integralModelFamily_isHermitian V).1 hp
  dsimp only [η] at he
  simpa only [integralModelFamily_globalUnitBallModule V] using he

/-- Original arithmetic sections of the literal finite global lattice are
exactly the original bundle's all-place effective vectors. -/
def integralModelEffectiveSectionsEquiv :
    effectiveSections (V.toNormFamily.globalUnitBallModule (hξ := hV.1))
      (integralModelFamily V) ≃ V.toNormFamily.effectiveSections where
  toFun m := ⟨m.val.val, by
    intro ω
    by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
    · exact m.val.property ω hω
    · have hm := m.property ω hω
      change V.toNormFamily.norm ω
        (1 ⊗ₜ[K] integralModelGenericEquiv V
          (genericInclusion (K := K) _ m.val)) ≤ 1 at hm
      rwa [integralModelGenericEquiv_original] at hm⟩
  invFun s := ⟨⟨s.val, fun ω _ => s.property ω⟩, by
    intro ω _
    change V.toNormFamily.norm ω
      (1 ⊗ₜ[K] integralModelGenericEquiv V
        (genericInclusion (K := K) _ ⟨s.val, fun ω _ => s.property ω⟩)) ≤ 1
    rw [integralModelGenericEquiv_original]
    exact s.property ω⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hV hpure in
/-- Finiteness of the actual all-place section set is produced from the
literal finite projective arithmetic model, rather than from a totalized count. -/
theorem effectiveSections_finite : V.toNormFamily.effectiveSections.Finite := by
  let := integralModel_finite V
  let := integralModel_projective V
  let L := V.toNormFamily.globalUnitBallModule (hξ := hV.1)
  have hf := finite_effectiveSections L (integralModelFamily V)
  let : Finite (effectiveSections L (integralModelFamily V)) := hf.to_subtype
  let : Finite V.toNormFamily.effectiveSections :=
    Finite.of_equiv _ (integralModelEffectiveSectionsEquiv V)
  exact Set.toFinite _

/-- The source arithmetic logarithmic count is the genuine finite all-place
section count of the original pure bundle. -/
theorem integralModel_logSectionCount :
    logSectionCount (V.toNormFamily.globalUnitBallModule (hξ := hV.1))
        (integralModelFamily V) =
      Real.log (Nat.card V.toNormFamily.effectiveSections : ℝ) := by
  unfold logSectionCount
  rw [Nat.card_congr (integralModelEffectiveSectionsEquiv V)]

/-- The actual original arithmetic model preserves determinant degree and
actual minimal slope, via its actual completed generic isometry. -/
theorem integralModel_degree_minimalSlope :
    letI := integralModel_finite V
    let L := V.toNormFamily.globalUnitBallModule (hξ := hV.1)
    let W := fullLatticeAdelicBundle (genericImage (K := K) L)
      (genericImage_fg L) (genericImage_fullSpan L) (integralModelFamily V)
    (W.degree =
      V.degree) ∧
    (W.minimalSlope =
      V.minimalSlope) := by
  let := integralModel_finite V
  let L := V.toNormFamily.globalUnitBallModule (hξ := hV.1)
  let W := fullLatticeAdelicBundle (genericImage (K := K) L)
    (genericImage_fg L) (genericImage_fullSpan L) (integralModelFamily V)
  let e := integralModelGenericEquiv V
  have he (ω) (x) : V.toNormFamily.norm ω
      (e.toLinearMap.baseChange ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion x) =
        W.toNormFamily.norm ω x := by
    change _ = (fullLatticeGaugeFamily _ _ _ _).norm ω x
    rw [integralModelFamily_eq_fullLatticeGaugeFamily]
    rfl
  exact ⟨W.degree_eq_of_completed_isometry V e
      he,
    W.minimalSlope_eq_of_completed_isometry V e
      he⟩

omit V hV hpure in
/-- The actual nonnegative HN bundle has an original finite projective
arithmetic model with the required h0, degree, minimal slope and rank. -/
theorem original_hnZero_arithmetic_model
    (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    let L := genericImage (K := K) M
    let hfg := genericImage_fg (K := K) M
    let hspan := genericImage_fullSpan (K := K) M
    let V := fullLatticeAdelicBundle L hfg hspan η
    let hV := fullLatticeGaugeFamily_isHermitian L hfg hspan η
    let F := V.hermitianHNFiltration
      (hV := hV) 0
    let W := V.restrictOfNormMeasurability F
    let hW := hV.restrict F
    let hpW := (fullLatticeGaugeFamily_isPureAtFinitePlaces L hfg hspan η).restrict F
    let A := W.toNormFamily.globalUnitBallModule (hξ := hW.1)
    let ζ := integralModelFamily W (hV := hW) (hpure := hpW)
    letI := integralModel_finite W (hV := hW) (hpure := hpW)
    let B := fullLatticeAdelicBundle (genericImage (K := K) A)
      (genericImage_fg A) (genericImage_fullSpan A) ζ
    (logSectionCount M η = logSectionCount A ζ) ∧
    (V.positiveDegree =
      (B.degree : EReal)) ∧
    (0 ≤ B.minimalSlope) ∧
    Module.finrank K (K ⊗[𝓞 K] A) ≤ Module.finrank K (K ⊗[𝓞 K] M) := by
  let L := genericImage (K := K) M
  let hfg := genericImage_fg (K := K) M
  let hspan := genericImage_fullSpan (K := K) M
  let V := fullLatticeAdelicBundle L hfg hspan η
  let hV := fullLatticeGaugeFamily_isHermitian L hfg hspan η
  let F := V.hermitianHNFiltration
    (hV := hV) 0
  let W := V.restrictOfNormMeasurability F
  let hW := hV.restrict F
  let hpW := (fullLatticeGaugeFamily_isPureAtFinitePlaces L hfg hspan η).restrict F
  let A := W.toNormFamily.globalUnitBallModule (hξ := hW.1)
  let ζ := integralModelFamily W (hV := hW) (hpure := hpW)
  let := integralModel_finite W (hV := hW) (hpure := hpW)
  have h := NumberFieldClassicalHNSections.original_hnZero_sections_degree_minimalSlope M η
  have hmodel := integralModel_degree_minimalSlope W (hV := hW) (hpure := hpW)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.1.trans (integralModel_logSectionCount W (hV := hW) (hpure := hpW)).symm
  · rw [hmodel.1]
    exact h.2.1
  · rw [hmodel.2]
    exact h.2.2
  · exact (integralModelGenericEquiv W (hV := hW) (hpure := hpW)).finrank_eq ▸ F.finrank_le

end ArakelovGeometry.NumberFieldClassicalRestrictionModel

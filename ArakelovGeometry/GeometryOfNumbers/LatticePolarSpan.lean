/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.GeometryOfNumbers.LatticeSpanningPolarCount
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-! # The actual lattice span of a polar body -/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.GeometryOfNumbers.LatticePolarSpan

open Module Set MeasureTheory
open LatticeSubspaceCoordinates LatticeSubspaceBasis LatticeSubspaceQuotient
open LatticeIntegralDualCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual real span of the actual integral-dual points of the actual polar. -/
def polarLatticeSpan (L : Submodule ℤ E) (C : Set E) : Submodule ℝ (StrongDual ℝ E) :=
  Submodule.span ℝ (StrongDual.polar ℝ C ∩ (integralDual L : Set (StrongDual ℝ E)))

/-- The actual polar lattice span is rational for the actual integral dual lattice. -/
theorem polarLatticeSpan_rational (L : Submodule ℤ E) (C : Set E) :
    Submodule.span ℝ ((integralDual L : Set (StrongDual ℝ E)) ∩
      (polarLatticeSpan L C : Set (StrongDual ℝ E))) = polarLatticeSpan L C := by
  apply le_antisymm (Submodule.span_le.mpr fun _ hx => hx.2)
  apply Submodule.span_le.mpr
  intro f hf
  exact Submodule.subset_span ⟨hf.2, Submodule.subset_span hf⟩

/-- All original polar lattice points, restricted to their literal span, and the inverse
inclusion are an actual bijection of the original body-point subtypes. -/
def polarLatticePointsEquivSection (L : Submodule ℤ E) (C : Set E) :
    {f : integralDual L // (f : StrongDual ℝ E) ∈ StrongDual.polar ℝ C} ≃
      {f : intersectionAsSubmodule (integralDual L) (polarLatticeSpan L C) //
        (f : polarLatticeSpan L C) ∈ (polarLatticeSpan L C).subtype ⁻¹' StrongDual.polar ℝ C} where
  toFun f := ⟨⟨⟨f.val, Submodule.subset_span ⟨f.property, f.val.property⟩⟩,
    f.val.property⟩, f.property⟩
  invFun f := ⟨⟨((f.val : polarLatticeSpan L C) : StrongDual ℝ E), f.val.property⟩,
    f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual full polar lattice count equals its actual intersection-section count. -/
theorem card_polar_eq_card_section (L : Submodule ℤ E) (C : Set E) :
    Nat.card {f : integralDual L // (f : StrongDual ℝ E) ∈ StrongDual.polar ℝ C} =
      Nat.card {f : intersectionAsSubmodule (integralDual L) (polarLatticeSpan L C) //
        (f : polarLatticeSpan L C) ∈
          (polarLatticeSpan L C).subtype ⁻¹' StrongDual.polar ℝ C} :=
  Nat.card_congr (polarLatticePointsEquivSection L C)

/-- The actual section lattice points span their actual subspace, with no supplied spanning
hypothesis and no regularity requirement on the original set. -/
theorem section_latticePoints_span (L : Submodule ℤ E) (C : Set E) :
    Submodule.span ℝ (((polarLatticeSpan L C).subtype ⁻¹' StrongDual.polar ℝ C) ∩
      (intersectionAsSubmodule (integralDual L) (polarLatticeSpan L C) :
        Set (polarLatticeSpan L C))) = ⊤ := by
  apply Submodule.map_injective_of_injective
    (f := (polarLatticeSpan L C).subtype) Subtype.val_injective
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  have hset : (polarLatticeSpan L C).subtype ''
      (((polarLatticeSpan L C).subtype ⁻¹' StrongDual.polar ℝ C) ∩
        (intersectionAsSubmodule (integralDual L) (polarLatticeSpan L C) :
          Set (polarLatticeSpan L C))) =
      StrongDual.polar ℝ C ∩ (integralDual L : Set (StrongDual ℝ E)) := by
    ext f
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hf
      exact ⟨⟨f, Submodule.subset_span hf⟩, hf, rfl⟩
  rw [hset]
  rfl

attribute [local instance] Submodule.closed_of_finiteDimensional

variable [FiniteDimensional ℝ E]

/-- The actual spanning producer applies to the actual polar section, after the literal
point-count equality and spanning hypotheses have both been derived. -/
theorem card_polar_mul_normalizedMeasure_section_polar_le_pow
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (C : Set E)
    [MeasurableSpace (polarLatticeSpan L C)] [BorelSpace (polarLatticeSpan L C)]
    [MeasurableSpace (StrongDual ℝ (polarLatticeSpan L C))]
    [BorelSpace (StrongDual ℝ (polarLatticeSpan L C))]
    (μ : Measure (StrongDual ℝ (polarLatticeSpan L C))) [μ.IsAddHaarMeasure]
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    (Nat.card {f : integralDual L // (f : StrongDual ℝ E) ∈ StrongDual.polar ℝ C} : ℝ) *
      (latticeNormalizedMeasure
        (integralDual (intersectionAsSubmodule (integralDual L) (polarLatticeSpan L C))) μ
        (StrongDual.polar ℝ ((polarLatticeSpan L C).subtype ⁻¹' StrongDual.polar ℝ C))).toReal ≤
      6 ^ Module.finrank ℝ (polarLatticeSpan L C) := by
  let := integralDual_discrete L
  let := integralDual_isZLattice L
  let U := polarLatticeSpan L C
  let := intersectionAsSubmodule_discrete (integralDual L) U (polarLatticeSpan_rational L C)
  let := intersectionAsSubmodule_isZLattice (integralDual L) U (polarLatticeSpan_rational L C)
  obtain ⟨hc, hcv, hs, hz, _⟩ := polar_body_properties hcompact hconvex hsymm hzero
  have hcS : IsCompact (U.subtype ⁻¹' StrongDual.polar ℝ C) :=
    (U.isClosedEmbedding_subtype U.closed_of_finiteDimensional).isCompact_preimage hc
  have hcvS := hcv.linear_preimage U.subtype
  have hsS : ∀ u ∈ U.subtype ⁻¹' StrongDual.polar ℝ C,
      -u ∈ U.subtype ⁻¹' StrongDual.polar ℝ C := by
    intro u hu
    exact hs u hu
  have h0S : (0 : U) ∈ U.subtype ⁻¹' StrongDual.polar ℝ C :=
    show (0 : StrongDual ℝ E) ∈ StrongDual.polar ℝ C from interior_subset hz
  rw [card_polar_eq_card_section]
  exact LatticeSpanningPolarCount.card_mul_normalizedMeasure_polar_le_pow
    (intersectionAsSubmodule (integralDual L) U) μ hcS hcvS hsS h0S
      (section_latticePoints_span L C)

/-- The canonical finite-dimensional evaluation equivalence to the actual continuous bidual. -/
def doubleDualEquiv : E ≃L[ℝ] StrongDual ℝ (StrongDual ℝ E) :=
  (LinearEquiv.ofBijective (NormedSpace.inclusionInDoubleDual ℝ E).toLinearMap
    ⟨(NormedSpace.inclusionInDoubleDualLi ℝ).injective, by
      intro g
      obtain ⟨x, hx⟩ := continuousDual_functional_eq_eval g
      exact ⟨x, ContinuousLinearMap.ext fun f => (hx f).symm⟩⟩).toContinuousLinearEquiv

@[simp]
theorem doubleDualEquiv_apply (x : E) (f : StrongDual ℝ E) :
    doubleDualEquiv x f = f x := rfl

/-- Canonical evaluation takes the original lattice onto its actual double integral dual. -/
theorem doubleDualEquiv_comap_integralDual (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.comap ℝ (integralDual (integralDual L)) doubleDualEquiv.toLinearMap = L := by
  classical
  let b := (Module.finBasis ℤ L).ofZLatticeBasis ℝ L
  have hb : Submodule.span ℤ (Set.range b) = L := Basis.ofZLatticeBasis_span ℝ L _
  ext x
  change (∀ f ∈ integralDual L, f x ∈ LinearMap.range (Algebra.linearMap ℤ ℝ)) ↔ x ∈ L
  constructor
  · intro hx
    rw [← hb, b.mem_span_iff_repr_mem ℤ]
    intro i
    have hf : continuousDualBasis b i ∈ integralDual L := by
      have heq : integralDual L = Submodule.span ℤ (Set.range (continuousDualBasis b)) :=
        (congrArg integralDual hb).symm.trans (integralDual_span b)
      rw [heq]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := hx _ hf
    exact ⟨n, by simpa only [continuousDualBasis_apply, Algebra.linearMap_apply] using hn⟩
  · intro hx f hf
    exact hf x hx

/-- Actual evaluation on a dual subspace, with no choice of inner product. -/
def subspaceEvaluation (U : Submodule ℝ (StrongDual ℝ E)) : E →L[ℝ] StrongDual ℝ U :=
  (dualRestriction U).comp doubleDualEquiv.toContinuousLinearMap

@[simp]
theorem subspaceEvaluation_apply (U : Submodule ℝ (StrongDual ℝ E)) (x : E) (f : U) :
    subspaceEvaluation U x f = (f : StrongDual ℝ E) x := rfl

/-- The actual primal annihilator of a dual subspace is the actual evaluation kernel. -/
def annihilator (U : Submodule ℝ (StrongDual ℝ E)) : Submodule ℝ E :=
  LinearMap.ker (subspaceEvaluation U).toLinearMap

/-- The evaluation-kernel definition is the literal intersection of the original kernels. -/
theorem annihilator_eq_iInf (U : Submodule ℝ (StrongDual ℝ E)) :
    annihilator U = ⨅ f : U, f.val.ker := by
  ext x
  change subspaceEvaluation U x = 0 ↔ _
  rw [Submodule.mem_iInf]
  constructor
  · intro hx f
    exact congrArg (fun g : StrongDual ℝ U => g f) hx
  · intro hx
    ext f
    exact hx f

section RationalSubspace

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (U : Submodule ℝ (StrongDual ℝ E))
  (hU : Submodule.span ℝ ((integralDual L : Set (StrongDual ℝ E)) ∩
    (U : Set (StrongDual ℝ E))) = U)

include hU in
/-- Surjectivity is produced from actual dual adapted coordinates and canonical evaluation. -/
theorem subspaceEvaluation_surjective : Function.Surjective (subspaceEvaluation U) := by
  let := integralDual_discrete L
  let := integralDual_isZLattice L
  intro g
  let d := LatticeDualCentralSection.dualAdaptedCoordinates (integralDual L) U hU
  refine ⟨doubleDualEquiv.symm (d (0, g)), ?_⟩
  change dualRestriction U (doubleDualEquiv (doubleDualEquiv.symm (d (0, g)))) = g
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact LatticeDualCentralSection.dualRestriction_dualAdaptedCoordinates
    (integralDual L) U hU (0, g)

/-- The actual quotient by the actual annihilator is canonically its original dual subspace's
continuous dual, by evaluation. -/
def quotientEvaluation : (E ⧸ annihilator U) ≃L[ℝ] StrongDual ℝ U :=
  ((subspaceEvaluation U).toLinearMap.quotKerEquivOfSurjective
    (subspaceEvaluation_surjective L U hU)).toContinuousLinearEquiv

@[simp]
theorem quotientEvaluation_apply_mk (x : E) :
    quotientEvaluation L U hU ((annihilator U).mkQ x) = subspaceEvaluation U x := rfl

/-- Canonical evaluation maps the actual original lattice onto its actual double integral dual. -/
theorem doubleDualEquiv_map_integralDual :
    L.map (doubleDualEquiv.toLinearMap.restrictScalars ℤ) = integralDual (integralDual L) := by
  conv_lhs => rw [← doubleDualEquiv_comap_integralDual L]
  exact Submodule.map_comap_eq_self
    (f := (doubleDualEquiv (E := E)).toLinearMap.restrictScalars ℤ) (by
    intro g _
    exact ⟨(doubleDualEquiv (E := E)).symm g,
      ContinuousLinearEquiv.apply_symm_apply (doubleDualEquiv (E := E)) g⟩)

include hU in
/-- The actual evaluation image of the original lattice is the actual intersection integral dual. -/
theorem subspaceEvaluation_map_lattice :
    L.map ((subspaceEvaluation U).toLinearMap.restrictScalars ℤ) =
      integralDual (intersectionAsSubmodule (integralDual L) U) := by
  let := integralDual_discrete L
  let := integralDual_isZLattice L
  rw [← integralDual_restriction_image (integralDual L) U hU,
    ← doubleDualEquiv_map_integralDual L]
  rw [← Submodule.map_comp]
  rfl

/-- The actual quotient lattice, not a supplied model, is exactly the pullback of the actual
intersection integral dual under the constructed quotient evaluation. -/
theorem quotientEvaluation_comap_lattice :
    ZLattice.comap ℝ (integralDual (intersectionAsSubmodule (integralDual L) U))
        (quotientEvaluation L U hU).toLinearMap = quotientImage L (annihilator U) := by
  ext q
  obtain ⟨x, rfl⟩ := (annihilator U).mkQ_surjective q
  change quotientEvaluation L U hU ((annihilator U).mkQ x) ∈
    integralDual (intersectionAsSubmodule (integralDual L) U) ↔ _
  rw [quotientEvaluation_apply_mk, ← subspaceEvaluation_map_lattice L U hU]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    change (annihilator U).mkQ y = (annihilator U).mkQ x
    apply (quotientEvaluation L U hU).injective
    rw [quotientEvaluation_apply_mk, quotientEvaluation_apply_mk]
    exact hxy
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    change (annihilator U).mkQ y = (annihilator U).mkQ x at hxy
    have h := congrArg (quotientEvaluation L U hU) hxy
    change subspaceEvaluation U y = subspaceEvaluation U x
    simpa only [quotientEvaluation_apply_mk] using h

include hU in
/-- The actual annihilator is rational for the actual primal lattice. This follows from the
full first integral-dual coordinate lattice, rather than being a supplied assumption. -/
theorem annihilator_rational :
    Submodule.span ℝ ((L : Set E) ∩ (annihilator U : Set E)) = annihilator U := by
  let := integralDual_discrete L
  let := integralDual_isZLattice L
  let := quotientImage_discrete (integralDual L) U hU
  let := quotientImage_isZLattice (integralDual L) U hU
  let := integralDual_discrete (quotientImage (integralDual L) U)
  let := integralDual_isZLattice (quotientImage (integralDual L) U)
  let K := integralDual (quotientImage (integralDual L) U)
  let d := LatticeDualCentralSection.dualAdaptedCoordinates (integralDual L) U hU
  let p : StrongDual ℝ ((StrongDual ℝ E) ⧸ U) →L[ℝ] E :=
    doubleDualEquiv.symm.toContinuousLinearMap.comp
      (d.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ (StrongDual ℝ ((StrongDual ℝ E) ⧸ U)) (StrongDual ℝ U)))
  have hpW (a : StrongDual ℝ ((StrongDual ℝ E) ⧸ U)) : p a ∈ annihilator U := by
    change dualRestriction U (doubleDualEquiv (doubleDualEquiv.symm (d (a, 0)))) = 0
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact LatticeDualCentralSection.dualRestriction_dualAdaptedCoordinates
      (integralDual L) U hU (a, 0)
  have hpL (a : StrongDual ℝ ((StrongDual ℝ E) ⧸ U)) (ha : a ∈ K) : p a ∈ L := by
    have hd : d (a, 0) ∈ integralDual (integralDual L) := by
      have h : (a, (0 : StrongDual ℝ U)) ∈
          ZLattice.comap ℝ (integralDual (integralDual L)) d.toLinearMap := by
        rw [LatticeDualCentralSection.dualAdaptedCoordinates_comap]
        exact ⟨ha, (integralDual (intersectionAsSubmodule (integralDual L) U)).zero_mem⟩
      exact h
    rw [← doubleDualEquiv_comap_integralDual L]
    change doubleDualEquiv (doubleDualEquiv.symm (d (a, 0))) ∈ integralDual (integralDual L)
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hd
  have hK : Submodule.span ℝ (K : Set (StrongDual ℝ ((StrongDual ℝ E) ⧸ U))) = ⊤ :=
    (inferInstance : IsZLattice ℝ K).span_top
  have hrange : p.toLinearMap.range ≤
      Submodule.span ℝ ((L : Set E) ∩ (annihilator U : Set E)) := by
    rw [← Submodule.map_top, ← hK, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.subset_span ⟨hpL a ha, hpW a⟩
  apply le_antisymm (Submodule.span_le.mpr fun _ hx => hx.2)
  intro x hx
  apply hrange
  let g := d.symm (doubleDualEquiv x)
  have hg2 : g.2 = 0 := by
    rw [LatticeDualCentralSection.dualAdaptedCoordinates_symm_snd]
    exact hx
  refine ⟨g.1, ?_⟩
  change doubleDualEquiv.symm (d (g.1, 0)) = x
  rw [← hg2, Prod.mk.eta, d.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

end RationalSubspace

/-- Canonical evaluation identifies the original closed symmetric convex body with its
actual continuous-dual bipolar. -/
theorem doubleDualEquiv_image_eq_bipolar {C : Set E}
    (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ C) :
    doubleDualEquiv '' C = StrongDual.polar ℝ (StrongDual.polar ℝ C) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩ f hf
    exact hf x hx
  · intro hg
    refine ⟨doubleDualEquiv.symm g, ?_, ContinuousLinearEquiv.apply_symm_apply _ _⟩
    rw [← bipolar_eq_of_closed_convex_symmetric hclosed hconvex hsymm hzero]
    intro f hf
    have h := hg f hf
    rw [← ContinuousLinearEquiv.apply_symm_apply doubleDualEquiv g] at h
    exact h

section QuotientBody

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  (U : Submodule ℝ (StrongDual ℝ E))
  (hU : Submodule.span ℝ ((integralDual L : Set (StrongDual ℝ E)) ∩
    (U : Set (StrongDual ℝ E))) = U)

include hU in
/-- Actual evaluation maps a body onto the intrinsic polar of its dual central section. -/
theorem subspaceEvaluation_image_eq_section_polar
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    subspaceEvaluation U '' C =
      StrongDual.polar ℝ (U.subtype ⁻¹' StrongDual.polar ℝ C) := by
  let := integralDual_discrete L
  let := integralDual_isZLattice L
  obtain ⟨hc, hcv, hs, hz, _⟩ := polar_body_properties hcompact hconvex hsymm hzero
  rw [← LatticeDualCentralSection.restriction_image_polar_eq_section_polar
    (integralDual L) U hU hc hcv hs hz,
    ← doubleDualEquiv_image_eq_bipolar hcompact.isClosed hconvex hsymm (interior_subset hzero),
    Set.image_image]
  rfl

/-- The canonical quotient evaluation carries the actual quotient body onto the actual
polar of the dual central section. -/
theorem quotientEvaluation_image_eq_section_polar
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    quotientEvaluation L U hU '' ((annihilator U).mkQ '' C) =
      StrongDual.polar ℝ (U.subtype ⁻¹' StrongDual.polar ℝ C) := by
  rw [Set.image_image]
  exact subspaceEvaluation_image_eq_section_polar L U hU hcompact hconvex hsymm hzero

variable [MeasurableSpace (E ⧸ annihilator U)] [BorelSpace (E ⧸ annihilator U)]
  [MeasurableSpace (StrongDual ℝ U)] [BorelSpace (StrongDual ℝ U)]

/-- The canonical quotient evaluation preserves the actual normalized lattice measures. -/
theorem measurePreserving_quotientEvaluation
    (μ : Measure (StrongDual ℝ U)) [μ.IsAddHaarMeasure]
    (ν : Measure (E ⧸ annihilator U)) [ν.IsAddHaarMeasure] :
    MeasurePreserving (quotientEvaluation L U hU)
      (latticeNormalizedMeasure (quotientImage L (annihilator U)) ν)
      (latticeNormalizedMeasure (integralDual (intersectionAsSubmodule (integralDual L) U)) μ) := by
  let := integralDual_discrete L
  let := integralDual_isZLattice L
  let := intersectionAsSubmodule_discrete (integralDual L) U hU
  let := intersectionAsSubmodule_isZLattice (integralDual L) U hU
  let := integralDual_discrete (intersectionAsSubmodule (integralDual L) U)
  let := integralDual_isZLattice (intersectionAsSubmodule (integralDual L) U)
  rw [← quotientEvaluation_comap_lattice L U hU]
  exact measurePreserving_latticeNormalizedMeasure_comap _ _ μ ν

include hU in
/-- The quotient volume equals the actual polar-section volume, with independently chosen
initial Haar measures normalized by the two literal lattices. -/
theorem normalizedMeasure_quotient_eq_section_polar
    (μ : Measure (StrongDual ℝ U)) [μ.IsAddHaarMeasure]
    (ν : Measure (E ⧸ annihilator U)) [ν.IsAddHaarMeasure]
    {C : Set E} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    latticeNormalizedMeasure (quotientImage L (annihilator U)) ν ((annihilator U).mkQ '' C) =
      latticeNormalizedMeasure (integralDual (intersectionAsSubmodule (integralDual L) U)) μ
        (StrongDual.polar ℝ (U.subtype ⁻¹' StrongDual.polar ℝ C)) := by
  let e := quotientEvaluation L U hU
  have hS : MeasurableSet (e '' ((annihilator U).mkQ '' C)) :=
    ((hcompact.image (annihilator U).mkQ.continuous_of_finiteDimensional).image
      e.continuous).isClosed.measurableSet
  have h := congrArg (fun τ : Measure (StrongDual ℝ U) =>
      τ (e '' ((annihilator U).mkQ '' C))) (measurePreserving_quotientEvaluation L U hU μ ν).map_eq
  rw [Measure.map_apply e.continuous.measurable hS,
    Set.preimage_image_eq _ e.injective,
    quotientEvaluation_image_eq_section_polar L U hU hcompact hconvex hsymm hzero] at h
  exact h

end QuotientBody

/-- All actual polar lattice points control the actual primal quotient volume by the
annihilator of their actual real span. No auxiliary measure or coordinate choice occurs in
the bound. -/
theorem card_polar_mul_normalizedMeasure_quotient_le_pow
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (C : Set E)
    [MeasurableSpace (E ⧸ annihilator (polarLatticeSpan L C))]
    [BorelSpace (E ⧸ annihilator (polarLatticeSpan L C))]
    (ν : Measure (E ⧸ annihilator (polarLatticeSpan L C))) [ν.IsAddHaarMeasure]
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hsymm : ∀ x ∈ C, -x ∈ C) (hzero : (0 : E) ∈ interior C) :
    (Nat.card {f : integralDual L // (f : StrongDual ℝ E) ∈ StrongDual.polar ℝ C} : ℝ) *
      (latticeNormalizedMeasure (quotientImage L (annihilator (polarLatticeSpan L C))) ν
        ((annihilator (polarLatticeSpan L C)).mkQ '' C)).toReal ≤
      6 ^ Module.finrank ℝ (polarLatticeSpan L C) := by
  let U := polarLatticeSpan L C
  let : MeasurableSpace U := borel _
  let : BorelSpace U := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ U) := borel _
  let : BorelSpace (StrongDual ℝ U) := ⟨rfl⟩
  let μ := (Module.finBasis ℝ (StrongDual ℝ U)).addHaar
  rw [normalizedMeasure_quotient_eq_section_polar L U (polarLatticeSpan_rational L C)
    μ ν hcompact hconvex hsymm hzero]
  exact card_polar_mul_normalizedMeasure_section_polar_le_pow L C μ
    hcompact hconvex hsymm hzero

end ArakelovGeometry.GeometryOfNumbers.LatticePolarSpan

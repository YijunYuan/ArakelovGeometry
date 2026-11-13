/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.UnitBall.Spanning

import ArakelovGeometry.NumberTheory.NumberField.Local.Lattice.Finite
import ArakelovGeometry.NumberTheory.NumberField.Model.Open.Localization

/-!
# Actual local unit-ball freeness and full rank

The literal rational coefficient ring is the actual principal integer ring
of its classified prime valuation. The produced scaled coefficient embedding
makes the actual rational unit ball free. Its produced finite basis extends
through the actual generic-fibre isomorphism to a rational basis of the
original vector space, proving full rank without global coherence.
-/

@[expose] public section

open scoped TensorProduct NumberField

noncomputable section

namespace ArakelovGeometry.AdelicStructure

universe u

variable {K : Type u} [Field K] [NumberField K] (S : AdelicStructure K)

/-- The actual rational coefficient ring is the actual principal integer ring
of its produced finite prime's integer-valued valuation. -/
theorem isPrincipalIdealRing_rationalLocalRing (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) : IsPrincipalIdealRing (S.rationalLocalRing ω hω) := by
  obtain ⟨p, hp⟩ := NumberField.exists_finitePlace_of_isNonarchimedean hnt hω
  rw [S.rationalLocalRing_eq_finitePlaceInteger ω hω p hp]
  infer_instance

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.NormFamily

open AdelicStructure

universe u w

variable {K : Type u} [Field K] [NumberField K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual scaled-coordinate image is a submodule of a finite free module
over the actual principal local coefficient ring, so the literal local ball is free. -/
theorem free_rationalUnitBallModule (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) [hξ : ξ.IsUltrametric] :
    Module.Free (S.rationalLocalRing ω hω) (ξ.rationalUnitBallModule ω hω) := by
  let := S.isPrincipalIdealRing_rationalLocalRing ω hω hnt
  let b := Module.finBasis K E
  obtain ⟨a, ha0, ha⟩ := ξ.exists_integral_dualBasis_unitBound b ω hω hnt
  let f := ξ.localUnitBallCoefficientEmbedding b ω hω a ha
  have hf : Function.Injective f :=
    ξ.localUnitBallCoefficientEmbedding_injective b ω hω a ha0 ha
  let e := LinearEquiv.ofInjective f hf
  let : Module.Free (S.rationalLocalRing ω hω) f.range := inferInstance
  exact Module.Free.of_equiv e.symm

/-- Native freeness at every finite parameter of the actual normalized curve. -/
theorem free_normalizedRationalUnitBallModule
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) [hξ : ξ.IsUltrametric] :
    Module.Free ((normalizedNumberFieldAdelicStructure K).rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω) :=
  ξ.free_rationalUnitBallModule ω hω
    (NormalizedNumberFieldPlaces.parameter_isNontrivial
      (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω))

/-- A finite basis of the actual free local unit-ball module, produced from
the genuine finite generation and freeness theorems. -/
def rationalLocalUnitBallBasis (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) [hξ : ξ.IsUltrametric] :
    Module.Basis (Fin (Module.finrank (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω))) (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω) := by
  letI := ξ.free_rationalUnitBallModule ω hω hnt
  letI : Module.Finite (S.rationalLocalRing ω hω) (ξ.rationalUnitBallModule ω hω) := by
    exact Module.Finite.iff_fg.mpr (ξ.fg_rationalUnitBallModule ω hω hnt)
  exact Module.finBasis _ _

/-- The actual local free basis extends through the proved intrinsic generic
fibre isomorphism to an actual basis of the original rational vector space. -/
def rationalLocalUnitBallGenericBasis (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) [hξ : ξ.IsUltrametric] :
    Module.Basis (Fin (Module.finrank (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω))) K E :=
  ((ξ.rationalLocalUnitBallBasis ω hω hnt).baseChange K).map
    (ξ.rationalUnitBallGenericFibreEquiv ω hω hnt)

@[simp]
theorem rationalLocalUnitBallGenericBasis_coe (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) (hnt : (S.ϕ ω).IsNontrivial) [hξ : ξ.IsUltrametric]
    (i : Fin (Module.finrank (S.rationalLocalRing ω hω)
      (ξ.rationalUnitBallModule ω hω))) :
    ξ.rationalLocalUnitBallGenericBasis ω hω hnt i =
      (ξ.rationalLocalUnitBallBasis ω hω hnt i : E) := by
  rw [rationalLocalUnitBallGenericBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply, ξ.rationalUnitBallGenericFibreEquiv_tmul, one_smul]

/-- The produced actual generic basis proves that the local unit-ball free
rank is exactly the original rational vector-space dimension. -/
theorem finrank_rationalUnitBallModule (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) [hξ : ξ.IsUltrametric] :
    Module.finrank (S.rationalLocalRing ω hω) (ξ.rationalUnitBallModule ω hω) =
      Module.finrank K E := by
  simpa only [Fintype.card_fin] using
    (Module.finrank_eq_card_basis (ξ.rationalLocalUnitBallGenericBasis ω hω hnt)).symm

end ArakelovGeometry.NormFamily

end

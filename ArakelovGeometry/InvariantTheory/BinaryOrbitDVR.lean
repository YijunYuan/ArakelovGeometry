/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.BinaryOrbitCoordinates
public import ArakelovGeometry.InvariantTheory.DVRWeights
public import ExternalResults.Stacks.StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.DiscreteValuationSpecialization
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Actual binary SL degeneration over a geometric DVR

For Bost p31 this module consumes polynomial closure of the actual A2 orbit.
The explicit coordinate morphism and the selected Stacks specialization produce
an actual fraction-field group element and all integral pure-tensor evaluations
needed by `DVRWeights`. The DVR is not assumed complete; neither a power-series
presentation nor algebraicity of its residue field over the ground field is used.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct
open MvPolynomial AlgebraicGeometry CategoryTheory

namespace ArakelovGeometry.InvariantTheory

universe u

variable {k : Type u} [Field k] {ι : Bool → Type u}
  [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)] {r : ℕ}

/-- The actual affine orbit morphism, parameterized by inverses. Its image is
exactly the actual dual A2 orbit; see `binaryCovector_inverse_orbit_image`. -/
def binaryOrbitMorphism (f : Module.Dual k (⨂[k]^r (⨂[k] j, (ι j → k)))) :=
  Spec.map (CommRingCat.ofHom (binaryCovectorOrbitPullback f).toRingHom)

instance binaryOrbitMorphism_locallyOfFiniteType
    (f : Module.Dual k (⨂[k]^r (⨂[k] j, (ι j → k)))) :
    LocallyOfFiniteType (binaryOrbitMorphism f) :=
  HasRingHomProperty.Spec_iff.mpr (binaryCovectorOrbitPullback_finiteType f)

instance binaryOrbitMorphism_quasiCompact
    (f : Module.Dual k (⨂[k]^r (⨂[k] j, (ι j → k)))) :
    QuasiCompact (binaryOrbitMorphism f) := by
  dsimp [binaryOrbitMorphism]
  infer_instance

/-- Literal output data of the geometric degeneration: the actual rings, scalar
tower, group element, and evaluations required by the existing Cartan theorem.
`nonempty_binaryCovectorDegeneration` produces these from polynomial orbit closure;
no DVR diagram or group lift is an input to that theorem. -/
structure BinaryCovectorDegeneration
    (f : Module.Dual k (⨂[k]^r (⨂[k] j, (ι j → k)))) where
  valuationRing : Type u
  fractionField : Type u
  [commRing : CommRing valuationRing]
  [isDomain : IsDomain valuationRing]
  [isDVR : IsDiscreteValuationRing valuationRing]
  [field : Field fractionField]
  [groundAlgebra : Algebra k valuationRing]
  [algebra : Algebra valuationRing fractionField]
  [groundFieldAlgebra : Algebra k fractionField]
  [scalarTower : IsScalarTower k valuationRing fractionField]
  [isFractionRing : IsFractionRing valuationRing fractionField]
  groupElement : ∀ j, Matrix.SpecialLinearGroup (ι j) fractionField
  integral : ∀ x : Fin r → ∀ j, ι j → valuationRing, ∃ c : valuationRing,
    binaryCovectorBaseChange fractionField f
      (⨂ₜ[fractionField] l, (⨂ₜ[fractionField] j,
        fun v ↦ algebraMap valuationRing fractionField (x l j v))) =
      algebraMap valuationRing fractionField c
  vanishes : ∀ x : Fin r → ∀ j, ι j → valuationRing,
    ∃ c ∈ IsLocalRing.maximalIdeal valuationRing,
      (tensorPowerRepresentation r
        (tensorSLRepresentation (k := fractionField) (fun j ↦ ι j → fractionField))).dual
        (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv (groupElement j))
        (binaryCovectorBaseChange fractionField f)
        (⨂ₜ[fractionField] l, (⨂ₜ[fractionField] j,
          fun v ↦ algebraMap valuationRing fractionField (x l j v))) =
        algebraMap valuationRing fractionField c

namespace BinaryCovectorDegeneration
attribute [instance] commRing isDomain isDVR field groundAlgebra algebra
  groundFieldAlgebra scalarTower isFractionRing
end BinaryCovectorDegeneration

omit [∀ j, DecidableEq (ι j)] in
/-- Basis evaluations in an ideal imply the full integral-pure-tensor condition.
The expansion uses the actual standard basis of the binary A2 tensor power. -/
theorem binaryCovector_integral_of_basis
    {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (I : Ideal R) (v : Module.Dual L (⨂[L]^r (⨂[L] j, (ι j → L))))
    (c : BinaryTensorIndex ι r → R) (hc : ∀ p, c p ∈ I)
    (hv : ∀ p, v (binaryTensorBasis L ι r p) = algebraMap R L (c p))
    (x : Fin r → ∀ j, ι j → R) : ∃ z ∈ I,
      v (⨂ₜ[L] l, (⨂ₜ[L] j, fun u ↦ algebraMap R L (x l j u))) =
        algebraMap R L z := by
  classical
  refine ⟨∑ p, c p * (∏ l, ∏ j, x l j (p l j)), ?_, ?_⟩
  · exact I.sum_mem fun p _ ↦ I.mul_mem_right _ (hc p)
  · rw [binaryCovector_eval_tprod]
    simp only [hv, map_sum, map_mul, map_prod]

/-- Polynomial closure of the actual binary orbit produces the actual DVR and
fraction-field SL element. This is the geometric implication needed by Bost p31,
not the full CM numerical equivalence. The Stacks diagram is constructed internally;
its commutativity supplies the ground-field structures. No completeness or
residue-field algebraicity is assumed or concluded. -/
theorem nonempty_binaryCovectorDegeneration
    (f : Module.Dual k (⨂[k]^r (⨂[k] j, (ι j → k))))
    (hclosure : ∀ P : MvPolynomial (BinaryTensorIndex ι r) k,
      (∀ g : ∀ j, _root_.SpecialLinearGroup k (ι j → k),
        MvPolynomial.eval (fun p ↦ (tensorPowerRepresentation r
          (tensorSLRepresentation (k := k) (fun j ↦ ι j → k))).dual g f
          (binaryTensorBasis k ι r p)) P = 0) → MvPolynomial.eval 0 P = 0) :
    Nonempty (BinaryCovectorDegeneration f) := by
  classical
  let y := binaryOrbitOrigin (k := k) (ι := ι) (r := r)
  obtain ⟨d⟩ := nonempty_discreteValuationSpecialization (binaryOrbitMorphism f) y
    (origin_mem_closure_specOrbit_of_actual_orbit_closure f hclosure)
  let R := d.valuationRing
  let L := d.fractionField
  let : CommRing R := d.commRing
  let : IsDomain R := d.isDomain
  let : IsDiscreteValuationRing R := d.isDVR
  let : Field L := d.field
  let : Algebra R L := d.algebra
  let : IsFractionRing R L := d.isFractionRing
  let ψ : MvPolynomial (BinaryTensorIndex ι r) k →+* R :=
    Spec.homEquivRingHom d.toTarget
  let χ : binarySLCoordinateAlgebra k ι →+* L := Spec.homEquivRingHom d.toSource
  have hcomm : (algebraMap R L).comp ψ = χ.comp (binaryCovectorOrbitPullback f).toRingHom := by
    have hh := congrArg Spec.preimage d.commutes
    change Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ d.toTarget) =
      Spec.preimage (d.toSource ≫ Spec.map
        (CommRingCat.ofHom (binaryCovectorOrbitPullback f).toRingHom)) at hh
    simp only [Spec.preimage_comp, Spec.preimage_map] at hh
    exact congrArg CommRingCat.Hom.hom hh
  let : Algebra k R := (ψ.comp MvPolynomial.C).toAlgebra
  let : Algebra k L := ((algebraMap R L).comp (ψ.comp MvPolynomial.C)).toAlgebra
  let : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let χa : binarySLCoordinateAlgebra k ι →ₐ[k] L :=
    { toRingHom := χ
      commutes' := by
        intro c
        change χ (algebraMap k (binarySLCoordinateAlgebra k ι) c) =
          algebraMap R L (ψ (MvPolynomial.C c))
        have hh := RingHom.congr_fun hcomm (MvPolynomial.C c)
        simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, ← MvPolynomial.algebraMap_eq,
          AlgHom.commutes] using hh.symm }
  let h := binarySLOfAlgHom χa
  have hψ (p : BinaryTensorIndex ι r) : ψ (X p) ∈ IsLocalRing.maximalIdeal R := by
    have ht : Spec.map (CommRingCat.ofHom ψ) = d.toTarget := Spec.map_preimage _
    have hm := d.maps_closedPoint
    rw [← ht] at hm
    change PrimeSpectrum.comap ψ ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ = y at hm
    have hy : X p ∈ y.asIdeal := by
      change aeval (0 : BinaryTensorIndex ι r → k) (X p) = 0
      simp
    rw [← hm] at hy
    exact hy
  have hv (p : BinaryTensorIndex ι r) :
      (tensorPowerRepresentation r
        (tensorSLRepresentation (k := L) (fun j ↦ ι j → L))).dual
        (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv ((h j)⁻¹))
        (binaryCovectorBaseChange L f) (binaryTensorBasis L ι r p) =
          algebraMap R L (ψ (X p)) := by
    rw [← binaryCovectorOrbitPullback_eval]
    change evalBinarySL (binarySLOfAlgHom χa) (binaryCovectorOrbitPullback f (X p)) = _
    rw [evalBinarySL_ofAlgHom]
    exact (RingHom.congr_fun hcomm (X p)).symm
  refine ⟨{
    valuationRing := R
    fractionField := L
    groupElement := fun j ↦ (h j)⁻¹
    integral := ?_
    vanishes := ?_ }⟩
  · intro x
    obtain ⟨c, -, hc⟩ := binaryCovector_integral_of_basis (⊤ : Ideal R)
      (binaryCovectorBaseChange L f)
      (fun p ↦ algebraMap k R (f (binaryTensorBasis k ι r p)))
      (fun _ ↦ trivial) (fun p ↦ by
        rw [binaryCovectorBaseChange_basis, IsScalarTower.algebraMap_apply k R L]) x
    exact ⟨c, hc⟩
  · exact binaryCovector_integral_of_basis (IsLocalRing.maximalIdeal R) _
      (fun p ↦ ψ (X p)) hψ hv

end ArakelovGeometry.InvariantTheory

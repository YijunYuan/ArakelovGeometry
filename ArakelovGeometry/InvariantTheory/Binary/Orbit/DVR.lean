/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.Binary.Orbit.Coordinates
public import ArakelovGeometry.InvariantTheory.DVR.Weights
public import ExternalCode.Stacks.StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.DiscreteValuationSpecialization
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

/-- The actual affine orbit morphism, parameterized by inverses. Over every extension field its
point image is exactly the actual dual A2 orbit; see `binaryCovector_inverse_orbit_image`. -/
def binaryOrbitMorphism (f : Module.Dual k (⨂[k]^r (⨂[k] j, (ι j → k)))) :
    Spec (CommRingCat.of (BinarySLCoordinateAlgebra k ι)) ⟶
      Spec (CommRingCat.of (MvPolynomial (BinaryTensorIndex ι r) k)) :=
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
  let χ : BinarySLCoordinateAlgebra k ι →+* L := Spec.homEquivRingHom d.toSource
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
  let χa : BinarySLCoordinateAlgebra k ι →ₐ[k] L :=
    { toRingHom := χ
      commutes' := by
        intro c
        change χ (algebraMap k (BinarySLCoordinateAlgebra k ι) c) =
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

namespace BinaryCovectorDegeneration

/-- An integral SL change of a nonzero ground-field covector has a nonzero
residue coordinate. This proves the primitivity needed for Bost, rather than
assuming nonempty residue support from integrality alone. -/
theorem exists_nonzero_residue_coordinate
    {f : Module.Dual k (⨂[k]^r (⨂[k] j, (ι j → k)))}
    (d : BinaryCovectorDegeneration f) (hf : f ≠ 0)
    (Q : ∀ j, Matrix.SpecialLinearGroup (ι j) d.valuationRing)
    (c : BinaryTensorIndex ι r → d.valuationRing)
    (hc : ∀ p,
      (tensorPowerRepresentation r
        (tensorSLRepresentation (k := d.fractionField) (fun j ↦ ι j → d.fractionField))).dual
        (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv
          (Matrix.SpecialLinearGroup.map (algebraMap d.valuationRing d.fractionField) (Q j)))
        (binaryCovectorBaseChange d.fractionField f)
        (binaryTensorBasis d.fractionField ι r p) =
      algebraMap d.valuationRing d.fractionField (c p)) :
    ∃ p, IsLocalRing.residue d.valuationRing (c p) ≠ 0 := by
  classical
  let R := d.valuationRing
  let L := d.fractionField
  let φ := algebraMap R L
  let ρ := (tensorPowerRepresentation r
    (tensorSLRepresentation (k := L) (fun j ↦ ι j → L))).dual
  let g := fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv
    (Matrix.SpecialLinearGroup.map φ (Q j))
  let fL := binaryCovectorBaseChange L f
  by_contra hn
  push Not at hn
  have hmem (p) : c p ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.residue_eq_zero_iff (c p)).mp (hn p)
  have hfull := binaryCovector_integral_of_basis (IsLocalRing.maximalIdeal R)
    (ρ g fL) c hmem hc
  have hback (x : Fin r → ∀ j, ι j → R) : ∃ z ∈ IsLocalRing.maximalIdeal R,
      fL (⨂ₜ[L] l, (⨂ₜ[L] j, fun u ↦ φ (x l j u))) = φ z := by
    obtain ⟨z, hz, he⟩ := binary_tensorPower_dual_preserves_integral_evaluations
      r (fun j ↦ (Q j)⁻¹) (IsLocalRing.maximalIdeal R) (ρ g fL) hfull x
    have hg : (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv
      (Matrix.SpecialLinearGroup.map φ ((Q j)⁻¹))) = g⁻¹ := by
      funext j
      simp [g]
    change ρ _ (ρ g fL) _ = φ z at he
    rw [hg, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at he
    exact ⟨z, hz, he⟩
  obtain ⟨p, hp⟩ : ∃ p, f (binaryTensorBasis k ι r p) ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hf
    apply (binaryTensorBasis k ι r).ext
    intro p
    exact hzero p
  obtain ⟨z, hz, he⟩ := hback (fun l j ↦ Pi.single (p l j) 1)
  have hxt : (⨂ₜ[L] l, (⨂ₜ[L] j,
      fun u : ι j ↦ φ ((Pi.single (p l j) (1 : R) : ι j → R) u))) =
      binaryTensorBasis L ι r p := by
    rw [binaryTensorBasis_apply]
    congr 1
    funext l
    congr 1
    funext j
    ext u
    simp [Pi.single_apply, apply_ite]
  rw [hxt] at he
  rw [binaryCovectorBaseChange_basis, IsScalarTower.algebraMap_apply k R L] at he
  have hez : algebraMap k R (f (binaryTensorBasis k ι r p)) = z :=
    IsFractionRing.injective R L he
  rw [← hez] at hz
  exact (IsLocalRing.notMem_maximalIdeal.mpr
    ((isUnit_iff_ne_zero.mpr hp).map (algebraMap k R))) hz

/-- The actual geometric output feeds the existing DVR Cartan theorem and gives
nonempty negative residue support, with zero-sum weights. The residue field remains
an arbitrary extension of the ground field; polynomial descent is separate. -/
theorem exists_negative_support
    {f : Module.Dual k (⨂[k]^r (⨂[k] j, (ι j → k)))}
    (d : BinaryCovectorDegeneration f) (hf : f ≠ 0) :
    ∃ (Q : ∀ j, Matrix.SpecialLinearGroup (ι j) d.valuationRing)
      (a : ∀ j, ι j → ℤ) (c : BinaryTensorIndex ι r → d.valuationRing),
      (∀ j, ∑ u, a j u = 0) ∧
      (∀ p,
        (tensorPowerRepresentation r
          (tensorSLRepresentation (k := d.fractionField) (fun j ↦ ι j → d.fractionField))).dual
          (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv
            (Matrix.SpecialLinearGroup.map (algebraMap d.valuationRing d.fractionField) (Q j)))
          (binaryCovectorBaseChange d.fractionField f)
          (binaryTensorBasis d.fractionField ι r p) =
          algebraMap d.valuationRing d.fractionField (c p)) ∧
      (∀ p, IsLocalRing.residue d.valuationRing (c p) ≠ 0 →
        (∑ l, ∑ j, a j (p l j)) < 0) ∧
      ∃ p, IsLocalRing.residue d.valuationRing (c p) ≠ 0 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible d.valuationRing
  obtain ⟨Q, a, ha, hs⟩ := exists_binary_cartan_negative_support hπ r
    d.groupElement (binaryCovectorBaseChange d.fractionField f) d.integral d.vanishes
  choose c hc hneg using hs
  have he (p) :
      (tensorPowerRepresentation r
        (tensorSLRepresentation (k := d.fractionField) (fun j ↦ ι j → d.fractionField))).dual
        (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv
          (Matrix.SpecialLinearGroup.map (algebraMap d.valuationRing d.fractionField) (Q j)))
        (binaryCovectorBaseChange d.fractionField f)
        (binaryTensorBasis d.fractionField ι r p) =
      algebraMap d.valuationRing d.fractionField (c p) := by
    simpa only [binaryTensorBasis_apply] using hc p
  exact ⟨Q, a, c, ha, he, hneg, d.exists_nonzero_residue_coordinate hf Q c he⟩

end BinaryCovectorDegeneration

section QuotientCoordinates

variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The scalar extension of a binary quotient in its chosen target basis.
This explicit basis transport retains all original quotient coefficients; the
following identities identify its actual determinant covector after extension. -/
def binaryQuotientCoordinateBaseChange (L : Type u) [Field L] [Algebra k L]
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] V) (b : Module.Basis (Fin r) k V) :
    (⨂[L] j, (ι j → L)) →ₗ[L] (Fin r → L) :=
  (Basis.piTensorProduct (fun j ↦ Pi.basisFun L (ι j))).constr L
    (fun p i ↦ algebraMap k L (b.coord i (q (⨂ₜ[k] j, Pi.single (p j) 1))))

@[simp]
theorem binaryQuotientCoordinateBaseChange_basis (L : Type u) [Field L] [Algebra k L]
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] V) (b : Module.Basis (Fin r) k V)
    (p : ∀ j, ι j) (i : Fin r) :
    binaryQuotientCoordinateBaseChange L q b (⨂ₜ[L] j, Pi.single (p j) 1) i =
      algebraMap k L (b.coord i (q (⨂ₜ[k] j, Pi.single (p j) 1))) := by
  have h := (Basis.piTensorProduct (fun j ↦ Pi.basisFun L (ι j))).constr_basis L
    (fun p i ↦ algebraMap k L (b.coord i (q (⨂ₜ[k] j, Pi.single (p j) 1)))) p
  simpa only [binaryQuotientCoordinateBaseChange, Basis.piTensorProduct_apply,
    Pi.basisFun_apply] using congrFun h i

/-- On every original pure tensor, the coordinate extension is the original
quotient followed by the target-basis coordinates and coefficient inclusion. -/
theorem binaryQuotientCoordinateBaseChange_tprod (L : Type u) [Field L] [Algebra k L]
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] V) (b : Module.Basis (Fin r) k V)
    (x : ∀ j, ι j → k) (i : Fin r) :
    binaryQuotientCoordinateBaseChange L q b
      (⨂ₜ[L] j, fun u ↦ algebraMap k L (x j u)) i =
      algebraMap k L (b.coord i (q (⨂ₜ[k] j, x j))) := by
  classical
  let β := Basis.piTensorProduct (fun j ↦ Pi.basisFun k (ι j))
  have he := congrArg (fun v ↦ algebraMap k L (b.coord i (q v)))
    (β.sum_repr (⨂ₜ[k] j, x j))
  rw [binaryQuotientCoordinateBaseChange, Module.Basis.constr_apply_fintype]
  simpa [β, Module.Basis.equivFun_apply, map_sum, map_smul, map_mul, map_prod,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he

/-- The actual determinant covector commutes with the explicit quotient basis
transport. Thus the covector used by the orbit producer is the actual A2 quotient
determinant over the fraction field, with no normalization or factorial. -/
theorem binaryQuotientCoordinateBaseChange_covector
    (L : Type u) [Field L] [Algebra k L]
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] V) (b : Module.Basis (Fin r) k V) :
    binaryCovectorBaseChange L
      (exteriorCovector r (exteriorPower.map r q.dualMap (exteriorPower.ιMulti k r b.coord))) =
    exteriorCovector r (exteriorPower.map r
      (binaryQuotientCoordinateBaseChange L q b).dualMap
      (exteriorPower.ιMulti L r (Pi.basisFun L (Fin r)).coord)) := by
  apply (binaryTensorBasis L ι r).ext
  intro p
  rw [binaryCovectorBaseChange_basis]
  simp only [binaryTensorBasis_apply, exteriorPower.map_apply_ιMulti,
    exteriorCovector_ιMulti_tprod]
  rw [(algebraMap k L).map_det]
  congr 1
  ext l i
  simp [binaryQuotientCoordinateBaseChange_basis]

omit [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)] in
/-- A surjective quotient has a nonzero actual determinant covector. -/
theorem binaryQuotientCovector_ne_zero
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] V) (b : Module.Basis (Fin r) k V)
    (hq : Function.Surjective q) :
    exteriorCovector r (exteriorPower.map r q.dualMap
      (exteriorPower.ιMulti k r b.coord)) ≠ 0 := by
  choose x hx using fun i ↦ hq (b i)
  intro hz
  have he := congrArg (fun f : Module.Dual k (⨂[k]^r (⨂[k] j, (ι j → k))) ↦
    f (⨂ₜ[k] i, x i)) hz
  simp only [exteriorPower.map_apply_ιMulti, exteriorCovector_ιMulti_tprod,
    LinearMap.zero_apply] at he
  change Matrix.det (Matrix.of fun i j ↦ b.coord j (q (x i))) = 0 at he
  have hmat : Matrix.of (fun i j ↦ b.coord j (q (x i))) =
      (1 : Matrix (Fin r) (Fin r) k) := by
    ext i j
    simp [hx, Finsupp.single_apply, Matrix.one_apply]
  rw [hmat, Matrix.det_one] at he
  exact one_ne_zero he

/-- The actual Bost quotient-determinant consumer. Polynomial closure produces
its own DVR and fraction-field group element, then Cartan gives actual integral
SL changes with nonempty negative residue support. The quotient over the fraction
field is the explicitly checked basis transport of the original quotient.
The residue field is arbitrary; this statement supplies the exact determinant
coordinates for subsequent polynomial solution descent. -/
theorem exists_binary_quotient_negative_support_of_orbit_closure
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] V) (b : Module.Basis (Fin r) k V)
    (hq : Function.Surjective q)
    (hclosure : ∀ P : MvPolynomial (BinaryTensorIndex ι r) k,
      (∀ g : ∀ j, _root_.SpecialLinearGroup k (ι j → k),
        MvPolynomial.eval (fun p ↦ (tensorPowerRepresentation r
          (tensorSLRepresentation (k := k) (fun j ↦ ι j → k))).dual g
          (exteriorCovector r (exteriorPower.map r q.dualMap
            (exteriorPower.ιMulti k r b.coord)))
          (binaryTensorBasis k ι r p)) P = 0) → MvPolynomial.eval 0 P = 0) :
    ∃ d : BinaryCovectorDegeneration (exteriorCovector r
        (exteriorPower.map r q.dualMap (exteriorPower.ιMulti k r b.coord))),
      ∃ (Q : ∀ j, Matrix.SpecialLinearGroup (ι j) d.valuationRing)
        (a : ∀ j, ι j → ℤ) (c : BinaryTensorIndex ι r → d.valuationRing),
        (∀ j, ∑ u, a j u = 0) ∧
        (∀ p, Matrix.det (Matrix.of fun l t ↦
          binaryQuotientCoordinateBaseChange d.fractionField q b
            (tensorSLRepresentation (k := d.fractionField) (fun j ↦ ι j → d.fractionField)
              (fun j ↦ (Matrix.SpecialLinearGroup.toLin'_equiv
                (Matrix.SpecialLinearGroup.map (algebraMap d.valuationRing d.fractionField)
                  (Q j)))⁻¹)
              (⨂ₜ[d.fractionField] j, Pi.single (p l j) 1)) t) =
          algebraMap d.valuationRing d.fractionField (c p)) ∧
        (∀ p, IsLocalRing.residue d.valuationRing (c p) ≠ 0 →
          (∑ l, ∑ j, a j (p l j)) < 0) ∧
        ∃ p, IsLocalRing.residue d.valuationRing (c p) ≠ 0 := by
  generalize hfdef : (exteriorCovector r
    (exteriorPower.map r q.dualMap (exteriorPower.ιMulti k r b.coord))) = f at hclosure ⊢
  have hf : f ≠ 0 := by
    rw [← hfdef]
    exact binaryQuotientCovector_ne_zero q b hq
  obtain ⟨d⟩ := nonempty_binaryCovectorDegeneration (k := k) (ι := ι) (r := r) f hclosure
  refine ⟨d, ?_⟩
  have hs := BinaryCovectorDegeneration.exists_negative_support
    (k := k) (ι := ι) (r := r) (f := f) d hf
  rcases hs with ⟨Q, a, c, ha, he, hn, hp⟩
  refine ⟨Q, a, c, ha, ?_, hn, hp⟩
  intro p
  have hh := he p
  have hfL := congrArg (binaryCovectorBaseChange d.fractionField) hfdef
  rw [binaryQuotientCoordinateBaseChange_covector] at hfL
  rw [← hfL] at hh
  simp only [binaryTensorBasis_apply, tensorPower_dual_quotientDeterminant_eval] at hh
  simpa [Module.Basis.coord_apply, Pi.inv_def] using hh

/-- The determinant polynomial over the original ground field. Matrix variables
are columns of the inverse integral Cartan factors; the output indices are rows.
These are precisely the equations selected by nonnegative original weight sums
in the separate residue-field polynomial descent. -/
def binaryQuotientDeterminantPolynomial
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] V) (b : Module.Basis (Fin r) k V)
    (p : BinaryTensorIndex ι r) : MvPolynomial (BinarySLVariables ι) k :=
  Matrix.det (fun l t ↦ ∑ s : ∀ j, ι j,
    C (b.coord t (q (⨂ₜ[k] j, Pi.single (s j) 1))) *
      ∏ j, X ⟨j, s j, p l j⟩)

/-- Evaluation of the original-coefficient determinant polynomial in any ground
field algebra. This includes the arbitrary DVR and its residue field. -/
theorem binaryQuotientDeterminantPolynomial_eval
    (S : Type*) [CommRing S] [Algebra k S]
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] V) (b : Module.Basis (Fin r) k V)
    (U : ∀ j, Matrix (ι j) (ι j) S) (p : BinaryTensorIndex ι r) :
    aeval (fun v : BinarySLVariables ι ↦ U v.1 v.2.1 v.2.2)
      (binaryQuotientDeterminantPolynomial q b p) =
      Matrix.det (fun l t ↦ ∑ s : ∀ j, ι j,
        algebraMap k S (b.coord t (q (⨂ₜ[k] j, Pi.single (s j) 1))) *
          ∏ j, U j (s j) (p l j)) := by
  let ev : MvPolynomial (BinarySLVariables ι) k →ₐ[k] S :=
    aeval (fun v ↦ U v.1 v.2.1 v.2.2)
  let M : Matrix (Fin r) (Fin r) (MvPolynomial (BinarySLVariables ι) k) :=
    fun l t ↦ ∑ s : ∀ j, ι j,
      C (b.coord t (q (⨂ₜ[k] j, Pi.single (s j) 1))) * ∏ j, X ⟨j, s j, p l j⟩
  have hM : ev.mapMatrix M = (fun l t ↦ ∑ s : ∀ j, ι j,
      algebraMap k S (b.coord t (q (⨂ₜ[k] j, Pi.single (s j) 1))) *
        ∏ j, U j (s j) (p l j)) := by
    ext l t
    change ev (M l t) = _
    simp [M, ev, map_sum]
  exact (ev.map_det M).trans (congrArg (Matrix.det (n := Fin r)) hM)

set_option backward.isDefEq.respectTransparency false in
/-- Over every extension field the polynomial evaluates to the actual transformed
quotient determinant. This identifies the original-k polynomial equations with
exactly the same A2 coordinates used by the geometric DVR and Cartan producer. -/
theorem binaryQuotientDeterminantPolynomial_actual_eval
    (L : Type u) [Field L] [Algebra k L]
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] V) (b : Module.Basis (Fin r) k V)
    (h : ∀ j, Matrix.SpecialLinearGroup (ι j) L) (p : BinaryTensorIndex ι r) :
    aeval (fun v : BinarySLVariables ι ↦ h v.1 v.2.1 v.2.2)
      (binaryQuotientDeterminantPolynomial q b p) =
    Matrix.det (Matrix.of fun l t ↦ binaryQuotientCoordinateBaseChange L q b
      (tensorSLRepresentation (k := L) (fun j ↦ ι j → L)
        (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv (h j))
        (⨂ₜ[L] j, Pi.single (p l j) 1)) t) := by
  trans Matrix.det (fun l t ↦ ∑ s : ∀ j, ι j,
    algebraMap k L (b.coord t (q (⨂ₜ[k] j, Pi.single (s j) 1))) *
      ∏ j, h j (s j) (p l j))
  · exact binaryQuotientDeterminantPolynomial_eval L q b (fun j ↦ (h j).val) p
  congr 1
  ext l t
  change _ = binaryQuotientCoordinateBaseChange L q b
    (PiTensorProduct.map (fun j ↦ (Matrix.SpecialLinearGroup.toLin'_equiv (h j)).val.toLinearMap)
      (⨂ₜ[L] j, Pi.single (p l j) 1)) t
  rw [PiTensorProduct.map_tprod]
  have hm (j : Bool) (v : ι j) :
      (Matrix.SpecialLinearGroup.toLin'_equiv (h j)).val (Pi.single v 1) =
        fun u ↦ h j u v := by
    change Matrix.mulVec (h j).val (Pi.single v 1) = _
    ext u
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp_rw [LinearEquiv.coe_coe, hm]
  rw [binaryQuotientCoordinateBaseChange, Module.Basis.constr_apply_fintype]
  simp [Module.Basis.equivFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_comm]


end QuotientCoordinates

end ArakelovGeometry.InvariantTheory

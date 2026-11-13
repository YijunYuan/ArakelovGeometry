/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.Binary.NegativeFiltration
public import ArakelovGeometry.InvariantTheory.Binary.OrbitSeparation
public import ArakelovGeometry.InvariantTheory.Binary.TensorTransport

/-!
# Actual binary geometric instability over an algebraically closed field

This is the binary, one-way implication required on Bost page 31. Quotient
Plücker nonsemistability produces actual centered negative real filtrations.
Factor coordinates are transported with the matrix/module SL group isomorphism,
and the actual quotient determinant is retained through orbit separation, DVR
degeneration and residue polynomial descent. Original-field optimizer descent
is the separate consumer in `Trivial.Filtration.Instability`.
-/

@[expose] public section

open scoped TensorProduct
open Module

noncomputable section

-- Prefer the canonical vector-space instance over the imported geometric module instances.
attribute [local instance 2000] Module.Free.of_divisionRing

namespace ArakelovGeometry.InvariantTheory

section Coordinates

variable {k : Type*} [Field k] {ι : Bool → Type*}
  [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)]
  {E : Bool → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]

/-- The actual product-group isomorphism for chosen factor coordinates.
It passes through matrix SL, so changing the factor bases also changes the group. -/
def binarySLCoordinates (b : ∀ j, Basis (ι j) k (E j)) :
    (∀ j, SpecialLinearGroup k (E j)) ≃*
      (∀ j, SpecialLinearGroup k (ι j → k)) :=
  MulEquiv.piCongrRight fun j ↦
    (Matrix.SpecialLinearGroup.toLin_equiv (b j)).symm.trans
      Matrix.SpecialLinearGroup.toLin'_equiv

/-- Coordinate action is conjugation by the actual basis equivalence. -/
theorem binarySLCoordinates_apply (b : ∀ j, Basis (ι j) k (E j))
    (g : ∀ j, SpecialLinearGroup k (E j)) (j : Bool) (x : E j) :
    binarySLCoordinates b g j ((b j).equivFun x) = (b j).equivFun (g j x) := by
  change Matrix.SpecialLinearGroup.toLin'_equiv
    ((Matrix.SpecialLinearGroup.toLin_equiv (b j)).symm (g j)) ((b j).equivFun x) = _
  simp [Matrix.SpecialLinearGroup.toLin_equiv, MulEquiv.symm_trans_apply,
    SpecialLinearGroup.congr_linearEquiv_symm]

/-- The tensor-power map induced by the chosen bases, without replacing the
underlying tensor representation. -/
def binaryTensorPowerCoordinates (b : ∀ j, Basis (ι j) k (E j)) (r : ℕ) :
    (⨂[k]^r (⨂[k] j, E j)) ≃ₗ[k] (⨂[k]^r (⨂[k] j, (ι j → k))) :=
  PiTensorProduct.congr fun _ : Fin r ↦ PiTensorProduct.congr fun j ↦ (b j).equivFun

/-- Chosen coordinates intertwine the actual positive tensor-power action with
the explicitly transported product of special linear groups. -/
theorem binaryTensorPowerCoordinates_equivariant
    (b : ∀ j, Basis (ι j) k (E j)) (r : ℕ)
    (g : ∀ j, SpecialLinearGroup k (E j)) (x : ⨂[k]^r (⨂[k] j, E j)) :
    binaryTensorPowerCoordinates b r (tensorPowerRepresentation r (tensorSLRepresentation E) g x) =
      tensorPowerRepresentation r (tensorSLRepresentation (fun j ↦ ι j → k))
        (binarySLCoordinates b g) (binaryTensorPowerCoordinates b r x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    simp only [map_smul]
    congr 1
    change PiTensorProduct.congr _ (PiTensorProduct.map _ _) =
      PiTensorProduct.map _ (PiTensorProduct.congr _ _)
    rw [PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod,
      PiTensorProduct.congr_tprod, PiTensorProduct.map_tprod]
    congr 1
    funext l
    induction x l using PiTensorProduct.induction_on with
    | smul_tprod c y =>
      simp only [map_smul]
      congr 1
      change PiTensorProduct.congr _ (PiTensorProduct.map _ _) =
        PiTensorProduct.map _ (PiTensorProduct.congr _ _)
      rw [PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod,
        PiTensorProduct.congr_tprod, PiTensorProduct.map_tprod]
      congr 1
      funext j
      exact (binarySLCoordinates_apply b g j (y j)).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/- The inverse is required for contravariant dual transport. -/
/-- Coordinates on actual tensor covectors, induced by the factor bases. -/
def binaryCovectorCoordinates (b : ∀ j, Basis (ι j) k (E j)) (r : ℕ) :
    Module.Dual k (⨂[k]^r (⨂[k] j, E j)) ≃ₗ[k]
      Module.Dual k (⨂[k]^r (⨂[k] j, (ι j → k))) :=
  (binaryTensorPowerCoordinates b r).symm.dualMap

/-- Actual contragredient actions are intertwined under the matrix/module SL
isomorphism; this is the group transport needed before invariant separation. -/
theorem binaryCovectorCoordinates_equivariant
    (b : ∀ j, Basis (ι j) k (E j)) (r : ℕ)
    (g : ∀ j, SpecialLinearGroup k (E j))
    (f : Module.Dual k (⨂[k]^r (⨂[k] j, E j))) :
    binaryCovectorCoordinates b r
        ((tensorPowerRepresentation r (tensorSLRepresentation E)).dual g f) =
      (tensorPowerRepresentation r (tensorSLRepresentation (fun j ↦ ι j → k))).dual
        (binarySLCoordinates b g) (binaryCovectorCoordinates b r f) := by
  apply LinearMap.ext
  intro x
  change f ((tensorPowerRepresentation r (tensorSLRepresentation E)) g⁻¹
      ((binaryTensorPowerCoordinates b r).symm x)) =
    f ((binaryTensorPowerCoordinates b r).symm
      ((tensorPowerRepresentation r (tensorSLRepresentation (fun j ↦ ι j → k)))
        (binarySLCoordinates b g)⁻¹ x))
  congr 1
  apply (binaryTensorPowerCoordinates b r).injective
  rw [binaryTensorPowerCoordinates_equivariant, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, map_inv]

variable [∀ j, FiniteDimensional k (E j)]

omit [∀ j, DecidableEq (ι j)] in
/-- Polynomial nonsemistability passes to factor coordinates using the actual
group isomorphism and polynomial pullback, not a change of chooseBasis alone. -/
theorem not_isPolynomialSemistable_binaryCovectorCoordinates
    (b : ∀ j, Basis (ι j) k (E j)) (r : ℕ)
    (f : Module.Dual k (⨂[k]^r (⨂[k] j, E j)))
    (hf : ¬ IsPolynomialSemistable (Module.Free.chooseBasis k _)
      (tensorPowerRepresentation r (tensorSLRepresentation E)).dual f) :
    ¬ IsPolynomialSemistable (Module.Free.chooseBasis k _)
      (tensorPowerRepresentation r (tensorSLRepresentation (fun j ↦ ι j → k))).dual
      (binaryCovectorCoordinates b r f) := by
  classical
  intro h
  let τ := (tensorPowerRepresentation r (tensorSLRepresentation (k := k)
    (fun j ↦ ι j → k))).dual
  have hres : IsPolynomialSemistable (Module.Free.chooseBasis k _)
      (τ.comp (binarySLCoordinates b).toMonoidHom) (binaryCovectorCoordinates b r f) := by
    obtain ⟨d, p, hd, hp, hi, hv⟩ := h
    exact ⟨d, p, hd, hp, fun g x ↦ hi (binarySLCoordinates b g) x, hv⟩
  exact hf (hres.of_map (Module.Free.chooseBasis k _) (Module.Free.chooseBasis k _)
    (τ.comp (binarySLCoordinates b).toMonoidHom)
    (tensorPowerRepresentation r (tensorSLRepresentation E)).dual
    (binaryCovectorCoordinates b r).toLinearMap
    (binaryCovectorCoordinates_equivariant b r) f)

variable {Q : Type*} [AddCommGroup Q] [Module k Q]

omit [∀ j, DecidableEq (ι j)] [∀ j, FiniteDimensional k (E j)] in
/-- The covector being tested after coordinate transport is precisely the
determinant covector of the original quotient precomposed with the basis tensor. -/
theorem binaryCovectorCoordinates_quotient
    (b : ∀ j, Basis (ι j) k (E j)) (r : ℕ) (d : Basis (Fin r) k Q)
    (q : (⨂[k] j, E j) →ₗ[k] Q) :
    binaryCovectorCoordinates b r (exteriorCovector r
      (exteriorPower.map r q.dualMap (exteriorPower.ιMulti k r d.coord))) =
    exteriorCovector r (exteriorPower.map r (binaryQuotientInCoordinates b q).dualMap
      (exteriorPower.ιMulti k r d.coord)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change exteriorCovector r (exteriorPower.map r q.dualMap
    (exteriorPower.ιMulti k r d.coord)) ((binaryTensorPowerCoordinates b r).symm
      (⨂ₜ[k] l, x l)) = _
  simp [binaryTensorPowerCoordinates, binaryQuotientInCoordinates]
  rfl

end Coordinates

section Quotient

variable {k : Type*} [Field k] [CharZero k] {ι : Bool → Type*}
  [∀ j, Fintype (ι j)]
  {E : Bool → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]
  [∀ j, FiniteDimensional k (E j)]
  {Q : Type*} [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q]

/-- Actual A2 quotient nonsemistability implies nonsemistability of the specific
determinant covector in factor coordinates. No extra nonzero certificate is
required: the target basis supplies its nonzero determinant generator. -/
theorem not_isPolynomialSemistable_binaryQuotientInCoordinates
    (b : ∀ j, Basis (ι j) k (E j)) (d : Basis (Fin (finrank k Q)) k Q)
    (q : (⨂[k] j, E j) →ₗ[k] Q)
    (hns : ¬ IsQuotientSemistable (tensorSLRepresentation E) q) :
    ¬ IsPolynomialSemistable (Module.Free.chooseBasis k _)
      (tensorPowerRepresentation (finrank k Q)
        (tensorSLRepresentation (fun j ↦ ι j → k))).dual
      (exteriorCovector (finrank k Q)
        (exteriorPower.map (finrank k Q) (binaryQuotientInCoordinates b q).dualMap
          (exteriorPower.ιMulti k (finrank k Q) d.coord))) := by
  rw [← binaryCovectorCoordinates_quotient]
  apply not_isPolynomialSemistable_binaryCovectorCoordinates
  intro h
  apply hns
  apply (isQuotientSemistable_iff_tensor (tensorSLRepresentation E) q).mpr
  refine ⟨exteriorPower.ιMulti k (finrank k Q) d.coord, ?_, ?_⟩
  · intro hz
    have he := congrArg (fun z ↦ exteriorCovector (finrank k Q) z
      (⨂ₜ[k] l, d l)) hz
    simp only [exteriorCovector_ιMulti_tprod, map_zero, LinearMap.zero_apply] at he
    have hm : Matrix.of (fun i j ↦ d.coord j (d i)) =
        (1 : Matrix (Fin (finrank k Q)) (Fin (finrank k Q)) k) := by
      ext i j
      simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    rw [hm, Matrix.det_one] at he
    exact one_ne_zero he
  · rwa [← exteriorCovector_map_dualMap]

end Quotient

section GeometricAssembly

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {E : Bool → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]
  [∀ j, FiniteDimensional k (E j)] [∀ j, Nontrivial (E j)]
  {Q : Type*} [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q]

/-- The binary geometric implication needed on Bost p31: actual A2 quotient
nonsemistability over an algebraically closed characteristic-zero field produces
actual centered finite left-continuous real filtrations with negative quotient
expectation. The proof composes invariant separation, the genuine DVR orbit
degeneration, original-coefficient residue polynomial descent and checked factor
coordinate transport. No group lift, negative candidate or extra nonzero
coordinate certificate is assumed. This is the one-way binary implication,
not a general-group Hilbert--Mumford converse; original-field normalization is
the subsequent Rationality consumer. -/
theorem exists_binary_negative_filtrations_of_not_isQuotientSemistable
    (q : (⨂[k] j, E j) →ₗ[k] Q) (hq : Function.Surjective q)
    (hQ : 0 < finrank k Q)
    (hns : ¬ IsQuotientSemistable (tensorSLRepresentation E) q) :
    ∃ P : ∀ j, ℝ → Submodule k (E j),
      (∀ j, Antitone (P j) ∧ (∃ t, P j t = ⊥) ∧ (∃ t, P j t = ⊤) ∧
        (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P j s = P j t) ∧
        Submodule.filtrationExpectation (P j) = 0) ∧
      Submodule.filtrationExpectation
        (fun t ↦ (Submodule.piTensorFiltration P t).map q) < 0 := by
  classical
  let ι j := ULift.{u} (Fin (finrank k (E j)))
  let b : ∀ j, Basis (ι j) k (E j) := fun j ↦
    (Module.finBasis k (E j)).reindex Equiv.ulift.symm
  let : ∀ j, Nonempty (ι j) := fun j ↦ ⟨ULift.up ⟨0, finrank_pos⟩⟩
  let d := Module.finBasis k Q
  let qc := binaryQuotientInCoordinates b q
  have hqc := binaryQuotientInCoordinates_surjective b q hq
  have hnsc := not_isPolynomialSemistable_binaryQuotientInCoordinates b d q hns
  obtain ⟨F, _, hneg, a, c, ha, hc⟩ :=
    exists_binary_negative_filtrations_of_orbit_closure qc d hqc hQ
      (binary_standard_orbit_zero_of_not_isPolynomialSemistable _ hnsc)
  let c' j := (c j).map (b j).equivFun.symm
  let w : ∀ j, ι j → ℝ := fun j i ↦ a j i
  let P : ∀ j, ℝ → Submodule k (E j) :=
    fun j t ↦ Submodule.span k (c' j '' {i | t ≤ w j i})
  refine ⟨P, ?_, ?_⟩
  · intro j
    obtain ⟨hb, ht⟩ := Submodule.span_weights_attains_bot_top (c' j) (w j)
    refine ⟨Submodule.antitone_span_weights (c' j) (w j), hb, ht,
      Submodule.span_weights_locallyConstant_left (c' j) (w j), ?_⟩
    rw [Submodule.filtrationExpectation_eq_sum_weights (c' j) (w j) (fun _ ↦ rfl)]
    have hs : ∑ i, w j i = 0 := by
      dsimp only [w]
      exact_mod_cast ha j
    rw [hs, zero_div]
  · have hF : (fun j t ↦ Submodule.span k (c j '' {i | t ≤ w j i})) = F :=
      funext fun j ↦ funext fun t ↦ (hc j t).symm
    have he (t : ℝ) := Submodule.piTensorFiltration_image_map_basis
      (fun j ↦ (b j).equivFun.symm) c w q t
    rw [hF] at he
    exact (congrArg Submodule.filtrationExpectation (funext he)).trans_lt hneg

end GeometricAssembly

end ArakelovGeometry.InvariantTheory

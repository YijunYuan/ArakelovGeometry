/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.OrbitSeparation
public import ArakelovGeometry.InvariantTheory.BinaryNegativeFiltration

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
  simp [binaryTensorPowerCoordinates, PiTensorProduct.congr_symm,
    binaryQuotientInCoordinates]

end Coordinates

end ArakelovGeometry.InvariantTheory

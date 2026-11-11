/-
Copyright (c) 2026 ArakelovGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArakelovGeometry contributors
-/
module

public import ArakelovGeometry.InvariantTheory.Semistability
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Determinant normalization of the general linear group

Over an algebraically closed field, every automorphism of a nonzero finite-dimensional
space is a scalar times a special linear automorphism. This is the group-theoretic
input to the determinant-twisted linearization comparison.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.InvariantTheory

open scoped TensorProduct

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]
  [FiniteDimensional k E]

/-- The canonical product action on a finite tensor product. -/
def tensorRepresentation {J : Type*} (E : J → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)] :
    Representation k (∀ j, E j ≃ₗ[k] E j) (⨂[k] j, E j) where
  toFun g := PiTensorProduct.map fun j ↦ (g j).toLinearMap
  map_one' := PiTensorProduct.map_id
  map_mul' g h := by
    simpa using PiTensorProduct.map_mul (fun j ↦ (g j).toLinearMap)
      (fun j ↦ (h j).toLinearMap)

/-- Restrict the tensor action to the product of the actual special linear groups. -/
def tensorSLRepresentation {J : Type*} (E : J → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)] :
    Representation k (∀ j, SpecialLinearGroup k (E j)) (⨂[k] j, E j) :=
  (tensorRepresentation E).comp
    { toFun := fun g j ↦ (g j).val
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }

/-- The tensor-power representation used for the determinant quotient point. -/
def tensorPowerRepresentation {G W : Type*} [Group G] [AddCommGroup W] [Module k W]
    (r : ℕ) (ρ : Representation k G W) : Representation k G (⨂[k]^r W) where
  toFun g := PiTensorProduct.map fun _ ↦ ρ g
  map_one' := by simp only [map_one]; exact PiTensorProduct.map_one
  map_mul' g h := by simp only [map_mul]; exact PiTensorProduct.map_mul _ _

omit [FiniteDimensional k E] in
/-- A scalar automorphism has determinant equal to the dimension power. -/
theorem det_smulOfUnit (c : kˣ) :
    (LinearEquiv.smulOfUnit c : E ≃ₗ[k] E).det = c ^ Module.finrank k E := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det ((c : k) • (LinearMap.id : E →ₗ[k] E)) = _
  simp

/-- Every automorphism is a scalar times a special linear automorphism over an
algebraically closed field, with the scalar's dimension power equal to its determinant. -/
theorem exists_smul_specialLinear [IsAlgClosed k] [Nontrivial E] (g : E ≃ₗ[k] E) :
    ∃ (c : kˣ) (h : SpecialLinearGroup k E),
      c ^ Module.finrank k E = g.det ∧ ∀ x, g x = (c : k) • h x := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (g.det : k)
    (Module.finrank_pos (R := k) (M := E))
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt (Module.finrank_pos (R := k) (M := E)))] at hc
    exact Units.ne_zero g.det hc.symm
  let u : kˣ := Units.mk0 c hc0
  let e : E ≃ₗ[k] E := g.trans (LinearEquiv.smulOfUnit u⁻¹)
  have hu : u ^ Module.finrank k E = g.det := by
    apply Units.ext
    exact hc
  have he : e.det = 1 := by
    change (LinearEquiv.smulOfUnit u⁻¹ * g).det = 1
    rw [map_mul, det_smulOfUnit, inv_pow, hu, inv_mul_cancel]
  refine ⟨u, ⟨e, he⟩, hu, ?_⟩
  intro x
  change g x = c • (c⁻¹ • g x)
  rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]

section Character

variable {J : Type*} [Fintype J] (E : J → Type*)
  [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]

/-- Central scalars act on a tensor product by their product. -/
theorem tensorRepresentation_scalar (c : J → kˣ) :
    tensorRepresentation E (fun j ↦ LinearEquiv.smulOfUnit (c j)) =
      (∏ j, (c j : k)) • LinearMap.id := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change PiTensorProduct.map (fun j ↦ (LinearEquiv.smulOfUnit (c j)).toLinearMap)
    (PiTensorProduct.tprod k x) = (∏ j, (c j : k)) • PiTensorProduct.tprod k x
  rw [PiTensorProduct.map_tprod]
  exact (PiTensorProduct.tprod k).map_smul_univ (fun j ↦ (c j : k)) x

/-- Central scalars on the tensor power have weight `r` in each factor. -/
theorem tensorPowerRepresentation_scalar (r : ℕ) (c : J → kˣ) :
    tensorPowerRepresentation r (tensorRepresentation E)
      (fun j ↦ LinearEquiv.smulOfUnit (c j)) =
      (∏ j, (c j : k)) ^ r • LinearMap.id := by
  change PiTensorProduct.map (fun _ : Fin r ↦
    tensorRepresentation E (fun j ↦ LinearEquiv.smulOfUnit (c j))) = _
  rw [tensorRepresentation_scalar]
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simpa using (PiTensorProduct.tprod k).map_smul_univ
    (fun _ : Fin r ↦ ∏ j, (c j : k)) x

/-- On tensor covectors the same central action has the inverse scalar weight. -/
theorem tensorPowerRepresentation_dual_scalar (r : ℕ) (c : J → kˣ) :
    (tensorPowerRepresentation r (tensorRepresentation E)).dual
      (fun j ↦ LinearEquiv.smulOfUnit (c j)) =
      ((∏ j, (c j : k))⁻¹) ^ r • LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  change f (tensorPowerRepresentation r (tensorRepresentation E)
    (fun j ↦ LinearEquiv.smulOfUnit (c j)⁻¹) x) = _
  rw [tensorPowerRepresentation_scalar]
  simp [Finset.prod_inv_distrib]

/-- The character of the determinant-dual twist in the quotient linearization. -/
def determinantTwist (r : ℕ) : (∀ j, E j ≃ₗ[k] E j) →* kˣ where
  toFun g := ∏ j, (g j).det⁻¹ ^
    (r * ((∏ i, Module.finrank k (E i)) / Module.finrank k (E j)))
  map_one' := by simp
  map_mul' g h := by
    simp [mul_pow, Finset.prod_mul_distrib, mul_comm]

/-- The determinant-dual character has central weight `-r A` in each factor. -/
theorem determinantTwist_scalar (r : ℕ) (c : J → kˣ) :
    determinantTwist E r (fun j ↦ LinearEquiv.smulOfUnit (c j)) =
      (∏ j, c j)⁻¹ ^ (r * ∏ j, Module.finrank k (E j)) := by
  classical
  have he (j : J) : Module.finrank k (E j) *
      (r * ((∏ i, Module.finrank k (E i)) / Module.finrank k (E j))) =
      r * ∏ i, Module.finrank k (E i) := by
    rw [Nat.mul_left_comm, Nat.mul_div_cancel']
    exact Finset.dvd_prod_of_mem (fun i ↦ Module.finrank k (E i)) (Finset.mem_univ j)
  simp only [determinantTwist, MonoidHom.coe_mk, OneHom.coe_mk, det_smulOfUnit,
    inv_pow, ← pow_mul, he, Finset.prod_pow, Finset.prod_inv_distrib]

/-- The polynomial section condition for the book's determinant-dual twist of
`O(A)`, on tensor covectors. -/
def IsDeterminantTwistedSemistable [∀ j, FiniteDimensional k (E j)]
    [∀ j, Nontrivial (E j)] (r : ℕ) (v : Module.Dual k (⨂[k]^r (⨂[k] j, E j))) :
    Prop :=
  ∃ (n : ℕ) (p : MvPolynomial (Module.Free.ChooseBasisIndex k
      (Module.Dual k (⨂[k]^r (⨂[k] j, E j)))) k),
    0 < n ∧ p.IsHomogeneous ((∏ j, Module.finrank k (E j)) * n) ∧
    (∀ g x, MvPolynomial.eval
      ((Module.Free.chooseBasis k _).repr
        ((tensorPowerRepresentation r (tensorRepresentation E)).dual g x)) p =
      (determinantTwist E r g : k) ^ n *
        MvPolynomial.eval ((Module.Free.chooseBasis k _).repr x) p) ∧
    MvPolynomial.eval ((Module.Free.chooseBasis k _).repr v) p ≠ 0

/-- Over an algebraically closed field, the actual special-linear invariant
condition equals the determinant-twisted general-linear section condition. -/
theorem isPolynomialSemistable_iff_determinantTwisted [IsAlgClosed k]
    [∀ j, FiniteDimensional k (E j)] [∀ j, Nontrivial (E j)]
    (r : ℕ) (v : Module.Dual k (⨂[k]^r (⨂[k] j, E j))) :
    IsPolynomialSemistable (Module.Free.chooseBasis k _)
      ((tensorPowerRepresentation r (tensorSLRepresentation E)).dual) v ↔
    IsDeterminantTwistedSemistable E r v := by
  classical
  let A := ∏ j, Module.finrank k (E j)
  let b := Module.Free.chooseBasis k (Module.Dual k (⨂[k]^r (⨂[k] j, E j)))
  have hA : 0 < A := Finset.prod_pos fun j _ ↦ Module.finrank_pos
  constructor
  · rintro ⟨d, p, hd, hp, hi, hv⟩
    refine ⟨d, p ^ A, hd, ?_, ?_, ?_⟩
    · simpa only [Nat.mul_comm] using hp.pow A
    · intro g x
      choose c h hc he using fun j ↦ exists_smul_specialLinear (g j)
      have hg : g = (fun j ↦ LinearEquiv.smulOfUnit (c j)) * (fun j ↦ (h j).val) := by
        funext j
        apply LinearEquiv.ext
        intro y
        exact he j y
      let a : k := (∏ j, (c j : k))⁻¹ ^ r
      have hact : (tensorPowerRepresentation r (tensorRepresentation E)).dual g x =
          a • (tensorPowerRepresentation r (tensorSLRepresentation E)).dual h x := by
        rw [hg, map_mul]
        change (tensorPowerRepresentation r (tensorRepresentation E)).dual
          (fun j ↦ LinearEquiv.smulOfUnit (c j))
          ((tensorPowerRepresentation r (tensorSLRepresentation E)).dual h x) = _
        rw [tensorPowerRepresentation_dual_scalar]
        rfl
      have hχ : (determinantTwist E r g : k) = a ^ A := by
        rw [hg, map_mul, determinantTwist_scalar]
        have hh : determinantTwist E r (fun j ↦ (h j).val) = 1 := by
          simp [determinantTwist]
        rw [hh, mul_one]
        simp [a, A, pow_mul]
      change MvPolynomial.eval (b.repr _) (p ^ A) =
        (determinantTwist E r g : k) ^ d * MvPolynomial.eval (b.repr x) (p ^ A)
      rw [hact, map_pow]
      simp only [map_smul, Finsupp.coe_smul]
      change MvPolynomial.eval (fun i ↦ a * b.repr
        ((tensorPowerRepresentation r (tensorSLRepresentation E)).dual h x) i) p ^ A = _
      rw [eval_smul_of_isHomogeneous hp, hi, mul_pow, hχ, map_pow]
      congr 1
      simp [← pow_mul, Nat.mul_comm]
    · simpa only [map_pow] using pow_ne_zero A hv
  · rintro ⟨n, p, hn, hp, hi, hv⟩
    refine ⟨A * n, p, Nat.mul_pos hA hn, hp, ?_, hv⟩
    intro g x
    have hh : determinantTwist E r (fun j ↦ (g j).val) = 1 := by
      simp [determinantTwist]
    have hres : (tensorPowerRepresentation r (tensorRepresentation E)).dual
        (fun j ↦ (g j).val) = (tensorPowerRepresentation r (tensorSLRepresentation E)).dual g := by
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro y
      rfl
    simpa only [hh, Units.val_one, one_pow, one_mul, hres] using hi (fun j ↦ (g j).val) x

end Character

end ArakelovGeometry.InvariantTheory

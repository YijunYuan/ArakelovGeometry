module

public import ArakelovGeometry.InvariantTheory.Semistability
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Actual polynomial actions in finite coordinates

Pullback by the inverse group element is the left action on the actual A2
coordinate polynomials. It preserves homogeneous components and bounded total
degree. These are the polynomial modules used for binary tensor invariant
separation in Bost p31, proof of Theorem 1.1. This file supplies no general
reductivity theorem, valuation-ring specialization or negative-weight criterion.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.InvariantTheory

open MvPolynomial

variable {k G M : Type*} [Field k] [Infinite k] [Group G]
  [AddCommGroup M] [Module k M] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Equality of actual coordinate polynomials can be tested on all vectors. -/
theorem polynomial_eq_of_eval_basis [Finite ι] (b : Module.Basis ι k M)
    {p q : MvPolynomial ι k}
    (h : ∀ x : M, eval (b.repr x) p = eval (b.repr x) q) : p = q := by
  classical
  let := Fintype.ofFinite ι
  apply MvPolynomial.funext
  intro x
  obtain ⟨v, hv⟩ := b.equivFun.surjective x
  simpa only [← hv, Module.Basis.equivFun_apply] using h v

/-- Pullback by the inverse gives the actual left polynomial representation.
For tensor covectors its degree-one action is the positive original tensor action. -/
def polynomialRepresentation (b : Module.Basis ι k M) (ρ : Representation k G M) :
    Representation k G (MvPolynomial ι k) where
  toFun g := (polynomialPullback b b (ρ g⁻¹)).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro p
    apply polynomial_eq_of_eval_basis b
    intro x
    change eval (b.repr x) (polynomialPullback b b (ρ 1⁻¹) p) = _
    simp [eval_polynomialPullback]
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    apply polynomial_eq_of_eval_basis b
    intro x
    change eval (b.repr x) (polynomialPullback b b (ρ (g * h)⁻¹) p) =
      eval (b.repr x) (polynomialPullback b b (ρ g⁻¹)
        (polynomialPullback b b (ρ h⁻¹) p))
    simp [eval_polynomialPullback, mul_inv_rev, Module.End.mul_apply]

@[simp]
theorem polynomialRepresentation_apply (b : Module.Basis ι k M)
    (ρ : Representation k G M) (g : G) (p : MvPolynomial ι k) :
    polynomialRepresentation b ρ g p = polynomialPullback b b (ρ g⁻¹) p := rfl

@[simp]
theorem eval_polynomialRepresentation (b : Module.Basis ι k M)
    (ρ : Representation k G M) (g : G) (p : MvPolynomial ι k) (x : M) :
    eval (b.repr x) (polynomialRepresentation b ρ g p) =
      eval (b.repr (ρ g⁻¹ x)) p := eval_polynomialPullback b b _ p x

/-- The actual polynomial action preserves each homogeneous degree. -/
theorem polynomialRepresentation_isHomogeneous (b : Module.Basis ι k M)
    (ρ : Representation k G M) (g : G) {p : MvPolynomial ι k} {d : ℕ}
    (hp : p.IsHomogeneous d) : (polynomialRepresentation b ρ g p).IsHomogeneous d :=
  polynomialPullback_isHomogeneous b b _ hp

/-- Homogeneous-component extraction commutes with the actual polynomial action.
This does not require an orbit-vanishing ideal to be homogeneous. -/
theorem polynomialRepresentation_homogeneousComponent (b : Module.Basis ι k M)
    (ρ : Representation k G M) (g : G) (d : ℕ) (p : MvPolynomial ι k) :
    polynomialRepresentation b ρ g (homogeneousComponent d p) =
      homogeneousComponent d (polynomialRepresentation b ρ g p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
    have hp := isHomogeneous_monomial (R := k) a (show m.degree = m.degree from rfl)
    rw [homogeneousComponent_of_mem hp,
      homogeneousComponent_of_mem (polynomialRepresentation_isHomogeneous b ρ g hp)]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add, hp, hq]

/-- The actual polynomial action does not increase total degree. -/
theorem polynomialRepresentation_totalDegree_le (b : Module.Basis ι k M)
    (ρ : Representation k G M) (g : G) (p : MvPolynomial ι k) :
    (polynomialRepresentation b ρ g p).totalDegree ≤ p.totalDegree := by
  classical
  have hp := sum_homogeneousComponent p
  calc
    (polynomialRepresentation b ρ g p).totalDegree =
        (∑ d ∈ Finset.range (p.totalDegree + 1),
          polynomialRepresentation b ρ g (homogeneousComponent d p)).totalDegree := by
      rw [← map_sum, hp]
    _ ≤ p.totalDegree := by
      apply (mem_restrictTotalDegree ι _ _).mp
      apply Submodule.sum_mem
      intro d hd
      apply (mem_restrictTotalDegree ι _ _).mpr
      exact (polynomialRepresentation_isHomogeneous b ρ g
        (homogeneousComponent_isHomogeneous d p)).totalDegree_le.trans
          (Nat.le_of_lt_succ (Finset.mem_range.mp hd))

/-- The actual action on bounded-degree polynomials, the finite module used
in the Bost p31 separation argument. -/
def boundedPolynomialRepresentation (b : Module.Basis ι k M)
    (ρ : Representation k G M) (D : ℕ) :
    Representation k G (restrictTotalDegree ι k D) where
  toFun g := (polynomialRepresentation b ρ g).restrict fun p hp ↦
    (mem_restrictTotalDegree ι D _).mpr
      ((polynomialRepresentation_totalDegree_le b ρ g p).trans
        ((mem_restrictTotalDegree ι D p).mp hp))
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact DFunLike.congr_fun ((polynomialRepresentation b ρ).map_one) p.val
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact DFunLike.congr_fun ((polynomialRepresentation b ρ).map_mul g h) p.val

/-- Fixed polynomials are exactly the pointwise A2 invariant polynomials. -/
theorem polynomialRepresentation_fixed_iff (b : Module.Basis ι k M)
    (ρ : Representation k G M) (p : MvPolynomial ι k) :
    (∀ g, polynomialRepresentation b ρ g p = p) ↔
      ∀ g x, eval (b.repr (ρ g x)) p = eval (b.repr x) p := by
  constructor
  · intro h g x
    have := congrArg (fun q ↦ eval (b.repr x) q) (h g⁻¹)
    simpa only [eval_polynomialRepresentation, inv_inv] using this
  · intro h g
    apply polynomial_eq_of_eval_basis b
    intro x
    rw [eval_polynomialRepresentation, h]

end ArakelovGeometry.InvariantTheory

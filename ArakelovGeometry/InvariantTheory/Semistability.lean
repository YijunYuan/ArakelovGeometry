module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Polynomial semistability

Positive-degree homogeneous invariant polynomials, with explicit coordinates.
The coordinate-change theorem makes the predicate independent of the chosen basis.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.InvariantTheory

open MvPolynomial

variable {k G M N : Type*} [Field k] [Group G]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {ι κ : Type*}

/-- Polynomial semistability for a representation, expressed in a chosen basis.
Over an algebraic closure this is the invariant-polynomial condition for geometric
semistability. No numerical criterion is built into the definition. -/
def IsPolynomialSemistable (b : Module.Basis ι k M) (ρ : Representation k G M)
    (v : M) : Prop :=
  ∃ (d : ℕ) (p : MvPolynomial ι k), 0 < d ∧ p.IsHomogeneous d ∧
    (∀ (g : G) (x : M), eval (b.repr (ρ g x)) p = eval (b.repr x) p) ∧
    eval (b.repr v) p ≠ 0

/-- Homogeneous polynomials acquire the degree power under scalar multiplication. -/
theorem eval_smul_of_isHomogeneous {p : MvPolynomial ι k} {d : ℕ}
    (hp : p.IsHomogeneous d) (c : k) (x : ι → k) :
    eval (fun i ↦ c * x i) p = c ^ d * eval x p := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hp.degree_eq_sum_deg_support hm]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/-- Nonzero rescaling does not change polynomial semistability. -/
theorem isPolynomialSemistable_smul_iff (b : Module.Basis ι k M)
    (ρ : Representation k G M) (v : M) {c : k} (hc : c ≠ 0) :
    IsPolynomialSemistable b ρ (c • v) ↔ IsPolynomialSemistable b ρ v := by
  unfold IsPolynomialSemistable
  simp only [map_smul, Finsupp.coe_smul]
  constructor
  · rintro ⟨d, p, hd, hp, hi, hv⟩
    refine ⟨d, p, hd, hp, hi, ?_⟩
    change eval (fun i ↦ c * b.repr v i) p ≠ 0 at hv
    rw [eval_smul_of_isHomogeneous hp] at hv
    exact (mul_ne_zero_iff.mp hv).2
  · rintro ⟨d, p, hd, hp, hi, hv⟩
    refine ⟨d, p, hd, hp, hi, ?_⟩
    change eval (fun i ↦ c * b.repr v i) p ≠ 0
    rw [eval_smul_of_isHomogeneous hp]
    exact mul_ne_zero (pow_ne_zero _ hc) hv

/-- Positive-degree homogeneous invariants vanish at the origin. -/
theorem not_isPolynomialSemistable_zero (b : Module.Basis ι k M)
    (ρ : Representation k G M) : ¬ IsPolynomialSemistable b ρ 0 := by
  rintro ⟨d, p, hd, hp, _, hv⟩
  have h := eval_smul_of_isHomogeneous hp 0 (fun _ ↦ 0)
  simp only [zero_mul, zero_pow (Nat.ne_of_gt hd), mul_zero] at h
  exact hv (by simpa using h)

/-- Pullback of an actual polynomial along a linear map, in specified bases. -/
def polynomialPullback [Fintype κ] (b : Module.Basis ι k M) (c : Module.Basis κ k N)
    (f : N →ₗ[k] M) : MvPolynomial ι k →ₐ[k] MvPolynomial κ k :=
  aeval fun i ↦ ∑ j, C (b.repr (f (c j)) i) * X j

/-- Substitution by linear forms preserves homogeneous degree. -/
theorem polynomialPullback_isHomogeneous [Fintype κ] (b : Module.Basis ι k M)
    (c : Module.Basis κ k N) (f : N →ₗ[k] M)
    {p : MvPolynomial ι k} {d : ℕ} (hp : p.IsHomogeneous d) :
    (polynomialPullback b c f p).IsHomogeneous d := by
  simpa only [one_mul, polynomialPullback] using hp.aeval
    (fun i ↦ ∑ j, C (b.repr (f (c j)) i) * X j)
    (fun i ↦ IsHomogeneous.sum _ _ 1 fun j _ ↦ isHomogeneous_C_mul_X _ _)

/-- Polynomial pullback agrees with composition on vectors. -/
theorem eval_polynomialPullback [Fintype κ] (b : Module.Basis ι k M)
    (c : Module.Basis κ k N) (f : N →ₗ[k] M) (p : MvPolynomial ι k) (x : N) :
    eval (c.repr x) (polynomialPullback b c f p) = eval (b.repr (f x)) p := by
  have h : (aeval (fun j ↦ c.repr x j)).comp (polynomialPullback b c f) =
      aeval (fun i ↦ b.repr (f x) i) := by
    ext i
    simp only [AlgHom.comp_apply, polynomialPullback, aeval_X, map_sum, map_mul,
      aeval_C]
    simpa only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, mul_comm, Algebra.algebraMap_self, RingHom.id_apply] using
      congrArg (fun y ↦ b.repr (f y) i) (c.sum_repr x)
  exact congrArg (fun q : MvPolynomial ι k →ₐ[k] k ↦ q p) h

/-- Equivariant pullback transports a nonvanishing invariant polynomial. -/
theorem IsPolynomialSemistable.of_map [Finite κ] (b : Module.Basis ι k M)
    (c : Module.Basis κ k N) (ρ : Representation k G M) (τ : Representation k G N)
    (f : N →ₗ[k] M) (hf : ∀ g x, f (τ g x) = ρ g (f x)) (v : N)
    (h : IsPolynomialSemistable b ρ (f v)) : IsPolynomialSemistable c τ v := by
  let := Fintype.ofFinite κ
  rcases h with ⟨d, p, hd, hp, hi, hv⟩
  refine ⟨d, polynomialPullback b c f p, hd,
    polynomialPullback_isHomogeneous b c f hp, ?_, ?_⟩
  · intro g x
    simp only [eval_polynomialPullback, hf, hi]
  · rwa [eval_polynomialPullback]

/-- The semistability predicate is independent of all coordinate choices. -/
theorem isPolynomialSemistable_basis_iff [Finite ι] [Finite κ] (b : Module.Basis ι k M)
    (c : Module.Basis κ k M) (ρ : Representation k G M) (v : M) :
    IsPolynomialSemistable b ρ v ↔ IsPolynomialSemistable c ρ v := by
  constructor
  · exact fun h ↦ h.of_map b c ρ ρ LinearMap.id (fun _ _ ↦ rfl) v
  · exact fun h ↦ h.of_map c b ρ ρ LinearMap.id (fun _ _ ↦ rfl) v

end ArakelovGeometry.InvariantTheory

module

public import ArakelovGeometry.InvariantTheory.PolynomialAction
public import ArakelovGeometry.InvariantTheory.Linearization
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

/-!
# Homogeneous polynomials as actual tensor quotients

Multiplication of the linear functions `w ↦ w(t)` is a surjective equivariant
map from the positive tensor power to homogeneous polynomials on the dual.
This concrete quotient is the bridge from fixed tensor-power semisimplicity
to the bounded polynomial modules in Bost p31. Arbitrary finite bases of the
dual are allowed, so the result retains the actual A2 polynomial coordinates.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.InvariantTheory

open MvPolynomial
open scoped TensorProduct Pointwise

variable {k T G : Type*} [Field k] [Infinite k] [AddCommGroup T] [Module k T]
  {ι : Type*} [Fintype ι]

/-- The actual linear polynomial on the dual obtained by evaluation at `t`. -/
def tensorLinearPolynomial (b : Module.Basis ι k (Module.Dual k T)) :
    T →ₗ[k] MvPolynomial ι k where
  toFun t := ∑ i, (b i t) • X i
  map_add' t u := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a t := by simp [smul_smul, Finset.smul_sum]

omit [Infinite k] in
/-- Evaluation of the coordinate polynomial is the actual dual pairing. -/
@[simp]
theorem eval_tensorLinearPolynomial (b : Module.Basis ι k (Module.Dual k T))
    (t : T) (w : Module.Dual k T) :
    eval (b.repr w) (tensorLinearPolynomial b t) = w t := by
  calc
    eval (b.repr w) (tensorLinearPolynomial b t) =
        (∑ i, b.repr w i • b i) t := by
      simp only [tensorLinearPolynomial, LinearMap.coe_mk, AddHom.coe_mk,
        map_sum, smul_eq_C_mul, map_mul, eval_C, eval_X,
        LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    _ = w t := congrArg (fun f : Module.Dual k T ↦ f t) (b.sum_repr w)

omit [Infinite k] in
/-- Tensor evaluation is homogeneous of degree one. -/
theorem tensorLinearPolynomial_isHomogeneous
    (b : Module.Basis ι k (Module.Dual k T)) (t : T) :
    (tensorLinearPolynomial b t).IsHomogeneous 1 := by
  exact (homogeneousSubmodule ι k 1).sum_mem fun i _ ↦
    (homogeneousSubmodule ι k 1).smul_mem _ (isHomogeneous_X k i)

/-- Linear polynomials on a finite-dimensional dual are exactly evaluations
at original vectors; in particular no extra dual-group inverse is introduced. -/
theorem tensorLinearPolynomial_range [FiniteDimensional k T]
    (b : Module.Basis ι k (Module.Dual k T)) :
    (tensorLinearPolynomial b).range = homogeneousSubmodule ι k 1 := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    exact tensorLinearPolynomial_isHomogeneous b t
  · rw [homogeneousSubmodule_one_eq_span_X]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨(Module.evalEquiv k T).symm (b.coord i), ?_⟩
    apply polynomial_eq_of_eval_basis b
    intro w
    simp [Module.apply_evalEquiv_symm_apply]

variable [Group G]

/-- The polynomial left action on the dual has the positive original action
on evaluation linear forms. -/
theorem tensorLinearPolynomial_equivariant
    (b : Module.Basis ι k (Module.Dual k T)) (ρ : Representation k G T)
    (g : G) (t : T) :
    tensorLinearPolynomial b (ρ g t) =
      polynomialRepresentation b ρ.dual g (tensorLinearPolynomial b t) := by
  apply polynomial_eq_of_eval_basis b
  intro w
  simp only [eval_tensorLinearPolynomial, eval_polynomialRepresentation]
  simp only [Representation.dual_apply, inv_inv]
  rfl

/-- Multiplication of evaluation linear forms on a tensor power. -/
def homogeneousTensorMap (b : Module.Basis ι k (Module.Dual k T)) (d : ℕ) :
    (⨂[k]^d T) →ₗ[k] MvPolynomial ι k :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra k (Fin d) (MvPolynomial ι k)).compLinearMap
      fun _ ↦ tensorLinearPolynomial b)

omit [Infinite k] in
@[simp]
theorem homogeneousTensorMap_tprod (b : Module.Basis ι k (Module.Dual k T))
    (d : ℕ) (t : Fin d → T) :
    homogeneousTensorMap b d (⨂ₜ[k] i, t i) = ∏ i, tensorLinearPolynomial b (t i) := by
  simp [homogeneousTensorMap, MultilinearMap.mkPiAlgebra_apply]

omit [Infinite k] in
/-- The multiplication map lands in the actual homogeneous submodule. -/
theorem homogeneousTensorMap_mem (b : Module.Basis ι k (Module.Dual k T))
    (d : ℕ) (t : ⨂[k]^d T) :
    homogeneousTensorMap b d t ∈ homogeneousSubmodule ι k d := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod a t =>
    rw [map_smul, homogeneousTensorMap_tprod]
    apply Submodule.smul_mem
    simpa using IsHomogeneous.prod (Finset.univ : Finset (Fin d))
      (fun i ↦ tensorLinearPolynomial b (t i)) (fun _ ↦ 1)
      (fun i _ ↦ tensorLinearPolynomial_isHomogeneous b (t i))
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- Multiplication is onto the whole homogeneous block, proved by the
power-of-linear-forms span identity, including degree zero. -/
theorem homogeneousTensorMap_range [FiniteDimensional k T]
    (b : Module.Basis ι k (Module.Dual k T)) (d : ℕ) :
    (homogeneousTensorMap b d).range = homogeneousSubmodule ι k d := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    exact homogeneousTensorMap_mem b d t
  · rw [← homogeneousSubmodule_one_pow, Submodule.pow_eq_span_pow_set]
    apply Submodule.span_le.mpr
    intro p hp
    obtain ⟨f, hf, rfl⟩ := Set.mem_pow_iff_prod.mp hp
    have hf' (i : Fin d) : f i ∈ (tensorLinearPolynomial b).range := by
      rw [tensorLinearPolynomial_range]
      exact hf i
    choose t ht using hf'
    exact ⟨PiTensorProduct.tprod k t, by simp [ht]⟩

/-- The homogeneous multiplication quotient is equivariant for the actual
positive tensor action and inverse-pullback action on dual polynomials. -/
theorem homogeneousTensorMap_equivariant
    (b : Module.Basis ι k (Module.Dual k T)) (ρ : Representation k G T)
    (d : ℕ) (g : G) (t : ⨂[k]^d T) :
    homogeneousTensorMap b d (tensorPowerRepresentation d ρ g t) =
      polynomialRepresentation b ρ.dual g (homogeneousTensorMap b d t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod a t =>
    simp only [map_smul]
    congr 1
    change homogeneousTensorMap b d (PiTensorProduct.map (fun _ ↦ ρ g)
      (PiTensorProduct.tprod k t)) = _
    rw [PiTensorProduct.map_tprod, homogeneousTensorMap_tprod, homogeneousTensorMap_tprod]
    simp only [tensorLinearPolynomial_equivariant, polynomialRepresentation_apply, map_prod]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The actual homogeneous block as a representation; no new polynomial model. -/
def homogeneousPolynomialRepresentation {M : Type*} [AddCommGroup M] [Module k M]
    (b : Module.Basis ι k M) (ρ : Representation k G M) (d : ℕ) :
    Representation k G (homogeneousSubmodule ι k d) where
  toFun g := (polynomialRepresentation b ρ g).restrict fun p hp ↦
    polynomialRepresentation_isHomogeneous b ρ g hp
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

/-- Surjectivity of multiplication with its actual homogeneous codomain. -/
theorem homogeneousTensorMap_surjective [FiniteDimensional k T]
    (b : Module.Basis ι k (Module.Dual k T)) (d : ℕ) :
    Function.Surjective ((homogeneousTensorMap b d).codRestrict
      (homogeneousSubmodule ι k d) (homogeneousTensorMap_mem b d)) := by
  intro p
  have hp : p.val ∈ (homogeneousTensorMap b d).range := by
    simpa only [homogeneousTensorMap_range] using p.property
  obtain ⟨t, ht⟩ := hp
  exact ⟨t, Subtype.ext ht⟩

end ArakelovGeometry.InvariantTheory

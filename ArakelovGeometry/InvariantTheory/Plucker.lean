module

public import ArakelovGeometry.InvariantTheory.Semistability
public import ArakelovGeometry.InvariantTheory.QuotientDeterminant
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Plücker semistability for tensor representations

The group and exterior actions are the canonical mathlib actions. Geometric
semistability is obtained by applying these definitions over an algebraic closure.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.InvariantTheory

open scoped TensorProduct

variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The representation on an exterior power, using the canonical exterior map. -/
def exteriorRepresentation (r : ℕ) (ρ : Representation k G W) :
    Representation k G (⋀[k]^r W) where
  toFun g := exteriorPower.map r (ρ g)
  map_one' := by
    rw [map_one]
    exact exteriorPower.map_id
  map_mul' g h := by
    rw [map_mul]
    exact exteriorPower.map_comp (ρ h) (ρ g)

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

/-- Plücker semistability of a linear map from a finite-dimensional space.
For a subspace use its inclusion; for a quotient use its dual inclusion. -/
def IsPluckerSemistable [FiniteDimensional k V] (ρ : Representation k G W)
    (i : V →ₗ[k] W) : Prop :=
  ∃ η : ⋀[k]^(Module.finrank k V) V, η ≠ 0 ∧
    IsPolynomialSemistable (Module.Free.chooseBasis k _)
      (exteriorRepresentation (Module.finrank k V) ρ)
      (exteriorPower.map (Module.finrank k V) i η)

/-- Any nonzero determinant vector tests the Plücker condition. -/
theorem isPluckerSemistable_iff [FiniteDimensional k V] (ρ : Representation k G W)
    (i : V →ₗ[k] W) {η : ⋀[k]^(Module.finrank k V) V} (hη : η ≠ 0) :
    IsPluckerSemistable ρ i ↔
      IsPolynomialSemistable (Module.Free.chooseBasis k _)
        (exteriorRepresentation (Module.finrank k V) ρ)
        (exteriorPower.map (Module.finrank k V) i η) := by
  constructor
  · rintro ⟨θ, hθ, h⟩
    obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one (finrank_topExterior (Q := V)) hη θ
    have hc : c ≠ 0 := by
      intro hc
      exact hθ (by simp [hc])
    rw [map_smul] at h
    exact (isPolynomialSemistable_smul_iff _ _ _ hc).mp h
  · exact fun h ↦ ⟨η, hη, h⟩

/-- Quotient semistability uses the contragredient action on the dual inclusion. -/
def IsQuotientSemistable [FiniteDimensional k V] (ρ : Representation k G W)
    (q : W →ₗ[k] V) : Prop :=
  IsPluckerSemistable ρ.dual q.dualMap

/-- The exterior pairing intertwines the two contragredient representations. -/
theorem pairingDual_equivariant (r : ℕ) (ρ : Representation k G W) (g : G)
    (z : ⋀[k]^r (Module.Dual k W)) :
    exteriorPower.pairingDual k W r (exteriorRepresentation r ρ.dual g z) =
      (exteriorRepresentation r ρ).dual g (exteriorPower.pairingDual k W r z) := by
  exact congrArg (fun f : (⋀[k]^r (Module.Dual k W)) →ₗ[k]
      Module.Dual k (⋀[k]^r W) ↦ f z) (pairingDual_map_dualMap r (ρ g⁻¹))

/-- The tensor-power representation used for the determinant quotient point. -/
def tensorPowerRepresentation (r : ℕ) (ρ : Representation k G W) :
    Representation k G (⨂[k]^r W) where
  toFun g := PiTensorProduct.map fun _ ↦ ρ g
  map_one' := by simp only [map_one]; exact PiTensorProduct.map_one
  map_mul' g h := by simp only [map_mul]; exact PiTensorProduct.map_mul _ _

/-- Tensor-to-exterior projection commutes with the representation. -/
theorem tensorToExterior_equivariant (r : ℕ) (ρ : Representation k G W) (g : G)
    (x : ⨂[k]^r W) :
    tensorToExterior k W r (tensorPowerRepresentation r ρ g x) =
      exteriorRepresentation r ρ g (tensorToExterior k W r x) := by
  have h : (tensorToExterior k W r).comp (tensorPowerRepresentation r ρ g) =
      (exteriorRepresentation r ρ g).comp (tensorToExterior k W r) := by
    apply PiTensorProduct.ext
    ext y
    simp [tensorPowerRepresentation, exteriorRepresentation, Function.comp_def]
  exact congrArg (fun f : (⨂[k]^r W) →ₗ[k] (⋀[k]^r W) ↦ f x) h

/-- The actual embedding of exterior covectors is equivariant. -/
theorem exteriorCovector_equivariant (r : ℕ) (ρ : Representation k G W) (g : G)
    (z : ⋀[k]^r (Module.Dual k W)) :
    exteriorCovector r (exteriorRepresentation r ρ.dual g z) =
      (tensorPowerRepresentation r ρ).dual g (exteriorCovector r z) := by
  ext x
  change exteriorPower.pairingDual k W r (exteriorRepresentation r ρ.dual g z)
      (tensorToExterior k W r x) =
    exteriorPower.pairingDual k W r z
      (tensorToExterior k W r (tensorPowerRepresentation r ρ g⁻¹ x))
  rw [pairingDual_equivariant, tensorToExterior_equivariant]
  rfl

/-- Geometric Plücker semistability of a tensor subspace, evaluated over the
algebraic closure and the full product of special linear groups there. -/
def IsGeometricallySemistableTensorSubspace {J : Type*} [Finite J] (E : J → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)] [FiniteDimensional k V]
    (i : V →ₗ[k] (⨂[k] j, E j)) : Prop :=
  IsPluckerSemistable
    (tensorSLRepresentation (fun j ↦ AlgebraicClosure k ⊗[k] E j))
    ((tensorBaseChangeEquiv k (AlgebraicClosure k) E).toLinearMap.comp
      (i.baseChange (AlgebraicClosure k)))

/-- Geometric semistability of a tensor quotient is the Plücker condition on
the scalar-extended dual inclusion, with the contragredient action. -/
def IsGeometricallySemistableTensorQuotient {J : Type*} [Finite J] (E : J → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)] [FiniteDimensional k V]
    (q : (⨂[k] j, E j) →ₗ[k] V) : Prop :=
  IsQuotientSemistable
    (tensorSLRepresentation (fun j ↦ AlgebraicClosure k ⊗[k] E j))
    ((q.baseChange (AlgebraicClosure k)).comp
      (tensorBaseChangeEquiv k (AlgebraicClosure k) E).symm.toLinearMap)

end ArakelovGeometry.InvariantTheory

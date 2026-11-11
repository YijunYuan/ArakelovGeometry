module

public import ArakelovGeometry.InvariantTheory.Semistability
public import ArakelovGeometry.InvariantTheory.QuotientDeterminant
public import ArakelovGeometry.InvariantTheory.Linearization
public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairMap
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

/-- Scalar extension of the tensor action agrees with the actual action of the
base-changed special linear automorphisms. -/
theorem tensorSLRepresentation_baseChange {J : Type*} [Finite J]
    (E : J → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]
    [∀ j, FiniteDimensional k (E j)] (L : Type*) [Field L] [Algebra k L]
    (g : ∀ j, SpecialLinearGroup k (E j)) (z : L ⊗[k] (⨂[k] j, E j)) :
    tensorBaseChangeEquiv k L E ((tensorSLRepresentation E g).baseChange L z) =
      tensorSLRepresentation (fun j ↦ L ⊗[k] E j)
        (fun j ↦ SpecialLinearGroup.baseChange (S := L) (g j))
        (tensorBaseChangeEquiv k L E z) := by
  exact tensorBaseChangeEquiv_map k L (fun j ↦ (g j).val.toLinearMap) z

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

/-- A nonzero rational determinant generator can be used to test the condition
after any field extension, through the canonical exterior base-change map. -/
theorem isPluckerSemistable_baseChange_iff [FiniteDimensional k V]
    (L : Type*) [Field L] [Algebra k L]
    (ρ : Representation L G (L ⊗[k] W)) (i : V →ₗ[k] W)
    (η : ⋀[k]^(Module.finrank k V) V) (hη : η ≠ 0) :
    let ηL := exteriorPowerDegreeEquiv L (L ⊗[k] V) Module.finrank_baseChange.symm
      (exteriorBaseChangeEquiv k L V (Module.finrank k V) ((1 : L) ⊗ₜ[k] η))
    IsPluckerSemistable ρ (i.baseChange L) ↔
      IsPolynomialSemistable (Module.Free.chooseBasis L _)
        (exteriorRepresentation (Module.finrank L (L ⊗[k] V)) ρ)
        (exteriorPower.map (Module.finrank L (L ⊗[k] V)) (i.baseChange L) ηL) := by
  dsimp only
  apply isPluckerSemistable_iff
  intro h
  have h₁ := (LinearEquiv.map_eq_zero_iff _).mp h
  have h₂ := (LinearEquiv.map_eq_zero_iff _).mp h₁
  apply hη
  apply Module.FaithfullyFlat.tensorProduct_mk_injective
    (A := k) (B := L) (⋀[k]^(Module.finrank k V) V)
  simpa using h₂

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
  apply LinearMap.ext
  intro x
  change exteriorPower.pairingDual k W r (exteriorRepresentation r ρ.dual g z)
      (tensorToExterior k W r x) =
    exteriorPower.pairingDual k W r z
      (tensorToExterior k W r (tensorPowerRepresentation r ρ g⁻¹ x))
  rw [pairingDual_equivariant, tensorToExterior_equivariant]
  rfl

/-- The canonical retraction of exterior covectors, obtained by alternating tensors. -/
def exteriorCovectorRetraction [FiniteDimensional k W] [CharZero k] (r : ℕ) :
    Module.Dual k (⨂[k]^r W) →ₗ[k] (⋀[k]^r (Module.Dual k W)) :=
  (LinearEquiv.ofBijective (exteriorPower.pairingDual k W r)
    (exteriorPower.bijective_pairingDual k W r)).symm.toLinearMap.comp
      (exteriorTensorSection (k := k) (W := W) r).dualMap

theorem pairingDual_exteriorCovectorRetraction [FiniteDimensional k W] [CharZero k]
    (r : ℕ) (f : Module.Dual k (⨂[k]^r W)) :
    exteriorPower.pairingDual k W r (exteriorCovectorRetraction r f) =
      (exteriorTensorSection r).dualMap f := by
  exact (LinearEquiv.ofBijective (exteriorPower.pairingDual k W r)
    (exteriorPower.bijective_pairingDual k W r)).apply_symm_apply _

/-- Alternating retraction is a left inverse on all exterior covectors. -/
theorem exteriorCovectorRetraction_leftInverse [FiniteDimensional k W] [CharZero k]
    (r : ℕ) (z : ⋀[k]^r (Module.Dual k W)) :
    exteriorCovectorRetraction r (exteriorCovector r z) = z := by
  apply (exteriorPower.bijective_pairingDual k W r).injective
  rw [pairingDual_exteriorCovectorRetraction]
  apply LinearMap.ext
  intro x
  change exteriorPower.pairingDual k W r z
    (tensorToExterior k W r (exteriorTensorSection r x)) = _
  rw [tensorToExterior_section]

/-- The alternating retraction commutes with the contragredient representations. -/
theorem exteriorCovectorRetraction_equivariant [FiniteDimensional k W] [CharZero k]
    (r : ℕ) (ρ : Representation k G W) (g : G) (f : Module.Dual k (⨂[k]^r W)) :
    exteriorCovectorRetraction r ((tensorPowerRepresentation r ρ).dual g f) =
      exteriorRepresentation r ρ.dual g (exteriorCovectorRetraction r f) := by
  apply (exteriorPower.bijective_pairingDual k W r).injective
  rw [pairingDual_exteriorCovectorRetraction, pairingDual_equivariant,
    pairingDual_exteriorCovectorRetraction]
  apply LinearMap.ext
  intro x
  change f (PiTensorProduct.map (fun _ : Fin r ↦ ρ g⁻¹) (exteriorTensorSection r x)) =
    f (exteriorTensorSection r (exteriorPower.map r (ρ g⁻¹) x))
  rw [exteriorTensorSection_map]

/-- The exterior and tensor presentations have the same semistable vectors. -/
theorem isPolynomialSemistable_exteriorCovector_iff [FiniteDimensional k W] [CharZero k]
    (r : ℕ) (ρ : Representation k G W) (z : ⋀[k]^r (Module.Dual k W)) :
    IsPolynomialSemistable (Module.Free.chooseBasis k _)
      ((tensorPowerRepresentation r ρ).dual) (exteriorCovector r z) ↔
    IsPolynomialSemistable (Module.Free.chooseBasis k _)
      (exteriorRepresentation r ρ.dual) z := by
  constructor
  · intro h
    exact IsPolynomialSemistable.of_map
      (Module.Free.chooseBasis k (Module.Dual k (⨂[k]^r W)))
      (Module.Free.chooseBasis k (⋀[k]^r (Module.Dual k W)))
      ((tensorPowerRepresentation r ρ).dual) (exteriorRepresentation r ρ.dual)
      (exteriorCovector r) (exteriorCovector_equivariant r ρ) z h
  · intro h
    exact IsPolynomialSemistable.of_map
      (Module.Free.chooseBasis k (⋀[k]^r (Module.Dual k W)))
      (Module.Free.chooseBasis k (Module.Dual k (⨂[k]^r W)))
      (exteriorRepresentation r ρ.dual) ((tensorPowerRepresentation r ρ).dual)
      (exteriorCovectorRetraction r)
      (exteriorCovectorRetraction_equivariant r ρ) (exteriorCovector r z)
      (by rwa [exteriorCovectorRetraction_leftInverse])

/-- Quotient Plücker semistability is the invariant-polynomial condition on the
actual tensor-to-determinant quotient covector. -/
theorem isQuotientSemistable_iff_tensor [FiniteDimensional k V] [FiniteDimensional k W]
    [CharZero k] (ρ : Representation k G W) (q : W →ₗ[k] V) :
    IsQuotientSemistable ρ q ↔
      ∃ η : ⋀[k]^(Module.finrank k V) (Module.Dual k V), η ≠ 0 ∧
        IsPolynomialSemistable (Module.Free.chooseBasis k _)
          ((tensorPowerRepresentation (Module.finrank k V) ρ).dual)
          ((quotientExterior (Module.finrank k V) q).dualMap
            (exteriorPower.pairingDual k V (Module.finrank k V) η)) := by
  have hd : Module.finrank k (Module.Dual k V) = Module.finrank k V := by simp
  let P (n : ℕ) : Prop := ∃ η : ⋀[k]^n (Module.Dual k V), η ≠ 0 ∧
    IsPolynomialSemistable (Module.Free.chooseBasis k (⋀[k]^n (Module.Dual k W)))
      (exteriorRepresentation n ρ.dual) (exteriorPower.map n q.dualMap η)
  change P (Module.finrank k (Module.Dual k V)) ↔ _
  rw [hd]
  dsimp only [P]
  apply exists_congr
  intro η
  apply and_congr_right
  intro _
  rw [← exteriorCovector_map_dualMap]
  exact (isPolynomialSemistable_exteriorCovector_iff _ ρ _).symm

/-- The quotient's dual Plücker condition is the book's determinant-twisted
polynomial section condition on its actual tensor-to-determinant covector. -/
theorem isQuotientSemistable_iff_determinantTwisted {J : Type*} [Fintype J]
    (E : J → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]
    [∀ j, FiniteDimensional k (E j)] [∀ j, Nontrivial (E j)]
    [IsAlgClosed k] [CharZero k] [FiniteDimensional k V]
    (q : (⨂[k] j, E j) →ₗ[k] V) :
    IsQuotientSemistable (tensorSLRepresentation E) q ↔
      ∃ η : ⋀[k]^(Module.finrank k V) (Module.Dual k V), η ≠ 0 ∧
        IsDeterminantTwistedSemistable E (Module.finrank k V)
          ((quotientExterior (Module.finrank k V) q).dualMap
            (exteriorPower.pairingDual k V (Module.finrank k V) η)) := by
  rw [isQuotientSemistable_iff_tensor]
  apply exists_congr
  intro η
  rw [isPolynomialSemistable_iff_determinantTwisted]

/-- Geometric Plücker semistability of a tensor subspace, evaluated over the
algebraic closure and the full product of special linear groups there. -/
def IsGeometricallySemistableTensorSubspace {J : Type*} [Finite J] (E : J → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]
    [∀ j, FiniteDimensional k (E j)] [∀ j, Nontrivial (E j)]
    [FiniteDimensional k V] [Nontrivial V]
    (i : V →ₗ[k] (⨂[k] j, E j)) : Prop :=
  IsPluckerSemistable
    (tensorSLRepresentation (fun j ↦ AlgebraicClosure k ⊗[k] E j))
    ((tensorBaseChangeEquiv k (AlgebraicClosure k) E).toLinearMap.comp
      (i.baseChange (AlgebraicClosure k)))

/-- Geometric semistability of a tensor quotient is the Plücker condition on
the scalar-extended dual inclusion, with the contragredient action. -/
def IsGeometricallySemistableTensorQuotient {J : Type*} [Finite J] (E : J → Type*)
    [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]
    [∀ j, FiniteDimensional k (E j)] [∀ j, Nontrivial (E j)]
    [FiniteDimensional k V] [Nontrivial V]
    (q : (⨂[k] j, E j) →ₗ[k] V) : Prop :=
  IsQuotientSemistable
    (tensorSLRepresentation (fun j ↦ AlgebraicClosure k ⊗[k] E j))
    ((q.baseChange (AlgebraicClosure k)).comp
      (tensorBaseChangeEquiv k (AlgebraicClosure k) E).symm.toLinearMap)

end ArakelovGeometry.InvariantTheory

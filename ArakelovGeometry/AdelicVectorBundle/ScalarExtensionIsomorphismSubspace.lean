/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionIsomorphismNorms

/-!
# Actual subspaces under field-isomorphism scalar transport

Field isomorphisms act semilinearly on actual scalar extensions and transport
their subspaces, ranks and completed vectors.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
variable {K L M E : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [AddCommGroup E] [Module K E]

/-- Literal scalar transport, semilinear over the actual extension fields. -/
def scalarExtensionSemilinearEquiv (σ : L ≃ₐ[K] M) :
    letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
    (L ⊗[K] E) ≃ₛₗ[(σ.toRingEquiv : L →+* M)] (M ⊗[K] E) := by
  letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  refine { (TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl K E)).toAddEquiv with
    map_smul' := ?_ }
  intro a z
  change TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl K E) (a • z) =
    σ a • TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl K E) z
  induction z using TensorProduct.inductionOn with
  | tmul b e =>
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]

/-- Transport is the prescribed isomorphism on the first pure coefficient. -/
@[simp]
theorem scalarExtensionSemilinearEquiv_tmul (σ : L ≃ₐ[K] M) (a : L) (z : E) :
    scalarExtensionSemilinearEquiv (E := E) σ (a ⊗ₜ[K] z) = σ a ⊗ₜ[K] z := rfl

/-- Actual extension-field subspaces correspond, with all order relations preserved. -/
def scalarExtensionSubspaceOrderIso (σ : L ≃ₐ[K] M) :
    Submodule L (L ⊗[K] E) ≃o Submodule M (M ⊗[K] E) := by
  letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  exact Submodule.orderIsoMapComap (scalarExtensionSemilinearEquiv (E := E) σ)

/-- Restriction to every actual subspace is semilinearly bijective onto its image. -/
def scalarExtensionSubspaceSemilinearEquiv (σ : L ≃ₐ[K] M)
    (B : Submodule L (L ⊗[K] E)) :
    letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
    B ≃ₛₗ[(σ.toRingEquiv : L →+* M)] scalarExtensionSubspaceOrderIso (E := E) σ B := by
  letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  exact (scalarExtensionSemilinearEquiv (E := E) σ).submoduleMap B

private theorem finrank_eq_of_semilinear
    {U V : Type*} [AddCommGroup U] [AddCommGroup V] [Module L U] [Module M V]
    [FiniteDimensional L U] (σ : L ≃+* M) :
    letI := RingHomInvPair.of_ringEquiv σ
    letI := RingHomInvPair.of_ringEquiv_symm σ
    ∀ _e : U ≃ₛₗ[(σ : L →+* M)] V, Module.finrank L U = Module.finrank M V := by
  intro e
  let := RingHomInvPair.of_ringEquiv σ
  let := RingHomInvPair.of_ringEquiv_symm σ
  let : Module L V := Module.compHom V (σ : L →+* M)
  let eL : U ≃ₗ[L] V := { e.toAddEquiv with map_smul' := e.map_smul' }
  let b := (Module.finBasis L U).map eL
  have h : ∀ (c : L) (x : V), σ c • x = c • x := fun _ _ ↦ rfl
  simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis (b.mapCoeffs σ h)).symm

/-- Every actual subspace has the same rank over the transported field. -/
theorem scalarExtensionSubspaceOrderIso_finrank [FiniteDimensional K E]
    (σ : L ≃ₐ[K] M) (B : Submodule L (L ⊗[K] E)) :
    Module.finrank M (scalarExtensionSubspaceOrderIso (E := E) σ B) = Module.finrank L B :=
  (finrank_eq_of_semilinear σ.toRingEquiv (scalarExtensionSubspaceSemilinearEquiv σ B)).symm

/-- Semilinear scalar transport preserves the subspace defining a relative quotient. -/
theorem scalarExtensionSubspace_map_kernel (σ : L ≃ₐ[K] M)
    (B T : Submodule L (L ⊗[K] E)) :
    letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
    (T.comap B.subtype).map (scalarExtensionSubspaceSemilinearEquiv σ B).toLinearMap =
      (scalarExtensionSubspaceOrderIso (E := E) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype := by
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨(b : L ⊗[K] E), hb, rfl⟩
  · intro hz
    obtain ⟨t, ht, he⟩ := hz
    obtain ⟨b, hb, hbe⟩ := z.property
    have htb : t = b := (scalarExtensionSemilinearEquiv (E := E) σ).injective
      (he.trans hbe.symm)
    subst t
    exact ⟨⟨b, hb⟩, ht, Subtype.ext hbe⟩

/-- Literal native subquotients, with their original extension-field scalar
structures, are semilinearly equivalent under the produced image correspondence. -/
def scalarExtensionSubquotientSemilinearEquiv (σ : L ≃ₐ[K] M)
    (B T : Submodule L (L ⊗[K] E)) :
    letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
    (B ⧸ T.comap B.subtype) ≃ₛₗ[(σ.toRingEquiv : L →+* M)]
      (scalarExtensionSubspaceOrderIso (E := E) σ B ⧸
        (scalarExtensionSubspaceOrderIso (E := E) σ T).comap
          (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype) := by
  letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  exact Submodule.Quotient.equiv _ _ (scalarExtensionSubspaceSemilinearEquiv σ B)
    (scalarExtensionSubspace_map_kernel σ B T)

/-- The native quotient correspondence is the prescribed map of actual classes. -/
theorem scalarExtensionSubquotientSemilinearEquiv_mk (σ : L ≃ₐ[K] M)
    (B T : Submodule L (L ⊗[K] E)) (b : B) :
    scalarExtensionSubquotientSemilinearEquiv σ B T (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (scalarExtensionSubspaceSemilinearEquiv σ B b) := rfl

/-- Every native transported subquotient retains its rank, including zero factors. -/
theorem scalarExtensionSubquotientSemilinearEquiv_finrank [FiniteDimensional K E]
    (σ : L ≃ₐ[K] M) (B T : Submodule L (L ⊗[K] E)) :
    Module.finrank M (scalarExtensionSubspaceOrderIso (E := E) σ B ⧸
      (scalarExtensionSubspaceOrderIso (E := E) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype) =
      Module.finrank L (B ⧸ T.comap B.subtype) :=
  (finrank_eq_of_semilinear σ.toRingEquiv
    (scalarExtensionSubquotientSemilinearEquiv σ B T)).symm

open AdelicStructure.ParameterSpaceExtension
variable {S : AdelicStructure K}

/-- Every rational tensor vector and every completed coefficient follow the
same genuine transport as the actual completed norm isometry. -/
theorem completedScalarExtensionAlgEquiv_rational (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (a : (pullbackAlgEquiv S σ x).abv.Completion) (z : L ⊗[K] E) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    completedScalarExtensionAlgEquiv (E := E) σ x (a ⊗ₜ[L] z) =
      algEquivCompletedFields S σ x a ⊗ₜ[M] scalarExtensionSemilinearEquiv (E := E) σ z := by
  intro aL aM
  let := aL
  let := aM
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  induction z using TensorProduct.inductionOn with
  | tmul b e => exact completedScalarExtensionAlgEquiv_tmul σ x a b e
  | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]

namespace NormFamily
variable [FiniteDimensional K E] [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]

/-- Every completed coefficient preserves the genuine scalar-extension norm
on every actual rational extension vector. -/
theorem scalarExtension_norm_tmul_algEquiv (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (a : (pullbackAlgEquiv S σ x).abv.Completion) (z : L ⊗[K] E) :
    (ξ.scalarExtension (L := M)).norm x
      (algEquivCompletedFields S σ x a ⊗ₜ[M] scalarExtensionSemilinearEquiv (E := E) σ z) =
      (ξ.scalarExtension (L := L)).norm (pullbackAlgEquiv S σ x) (a ⊗ₜ[L] z) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  have h := ξ.scalarExtension_norm_algEquiv σ x (a ⊗ₜ[L] z)
  rw [completedScalarExtensionAlgEquiv_rational] at h
  exact h

/-- Equality of the actual norm profiles on every rational extension vector. -/
theorem scalarExtension_norm_rational_algEquiv (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M) (z : L ⊗[K] E) :
    (ξ.scalarExtension (L := M)).norm x
      ((1 : x.abv.Completion) ⊗ₜ[M] scalarExtensionSemilinearEquiv (E := E) σ z) =
      (ξ.scalarExtension (L := L)).norm (pullbackAlgEquiv S σ x)
        ((1 : (pullbackAlgEquiv S σ x).abv.Completion) ⊗ₜ[L] z) := by
  simpa only [map_one] using ξ.scalarExtension_norm_tmul_algEquiv σ x
    (1 : (pullbackAlgEquiv S σ x).abv.Completion) z

end NormFamily

end ArakelovGeometry

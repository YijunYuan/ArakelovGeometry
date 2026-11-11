/-
Copyright (c) 2026 ArakelovGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArakelovGeometry contributors
-/
module

public import ArakelovGeometry.InvariantTheory.Linearization
public import ExternalResults.EtingofRepresentationTheory.PiTensorProduct.MapSpanCentralizer
public import Mathlib.RepresentationTheory.Semisimple

/-!
# Semisimplicity of actual special-linear tensor powers

Over an algebraically closed characteristic-zero field, the actual representation
of SpecialLinearGroup k E on each fixed tensor power of a nonzero finite-dimensional
space is semisimple. Degree zero is included. The selected Schur--Weyl producers
identify the GL tensor-map span with a semisimple image algebra; the existing
exists_smul_specialLinear identifies its span with the SL span in that degree.

This is the specific representation-theory input for the binary instability
branch of Bost, p31 (proof of Theorem 1.1). It specializes the general reductivity
input to tensor powers and their subquotients. The bounded-polynomial quotient,
two-factor regrouping, and actual orbit-ideal separation remain separate bridges.
No semisimplicity of the infinite group's group algebra is asserted.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open RepresentationTheory.Auxiliary.MutualCentralizers
open RepresentationTheory.PiTensorProduct.MapSpanCentralizer

namespace ArakelovGeometry.InvariantTheory

variable (k E : Type*) [Field k] [AddCommGroup E] [Module k E]

/-- The actual diagonal SL action on one tensor degree, including degree zero.
This is the fixed-degree representation used in the Bost p31 instability route. -/
def tensorPowerSLRepresentation (n : ℕ) :
    Representation k (SpecialLinearGroup k E) (⨂[k]^n E) where
  toFun g := PiTensorProduct.map fun _ ↦ g.val.toLinearMap
  map_one' := PiTensorProduct.map_one
  map_mul' _ _ := PiTensorProduct.map_mul _ _

private theorem representation_range_eq_span {G V : Type*} [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    ρ.asAlgebraHom.range.toSubmodule = Submodule.span k (Set.range ρ) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    induction f using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
    | single g c =>
      change ρ.asAlgebraHom (MonoidAlgebra.single g c) ∈ _
      rw [Representation.asAlgebraHom_single]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.single g 1, ρ.asAlgebraHom_single_one g⟩

private theorem representation_isSemisimpleModule_of_image {G V : Type*} [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    [IsSemisimpleRing ρ.asAlgebraHom.range] :
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule := by
  let f := ρ.asAlgebraHom.toRingHom.rangeRestrict
  have : RingHomSurjective f := ⟨ρ.asAlgebraHom.toRingHom.rangeRestrict_surjective⟩
  let e : ρ.asModule →ₛₗ[f] V :=
    { ρ.asModuleEquiv.toAddMonoidHom with map_smul' := fun _ _ ↦ rfl }
  exact (e.isSemisimpleModule_iff_of_bijective ρ.asModuleEquiv.bijective).mpr
    (inferInstance : IsSemisimpleModule ρ.asAlgebraHom.range V)

variable [FiniteDimensional k E] [IsAlgClosed k] [Nontrivial E]

/-- At each fixed degree the actual SL and GL tensor-map spans agree.
The determinant normalization contributes the scalar c^n; this theorem
does not assert equality on a sum of distinct degrees. This is the precise
GL-to-SL bridge needed by the Bost p31 tensor-power input. -/
theorem tensorPowerSL_span_eq_gl_span (n : ℕ) :
    Submodule.span k (Set.range (tensorPowerSLRepresentation k E n)) =
      Submodule.span k (Set.range fun g : E ≃ₗ[k] E ↦
        PiTensorProduct.map fun _ : Fin n ↦ g.toLinearMap) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact Submodule.subset_span ⟨g.val, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    obtain ⟨c, h, _, he⟩ := exists_smul_specialLinear g
    have hg : g.toLinearMap = (c : k) • h.val.toLinearMap := by
      ext x
      exact he x
    change PiTensorProduct.map (fun _ : Fin n ↦ g.toLinearMap) ∈ _
    rw [hg]
    have hmap :
        PiTensorProduct.map (fun _ : Fin n ↦ (c : k) • h.val.toLinearMap) =
          (c : k) ^ n • tensorPowerSLRepresentation k E n h := by
      change PiTensorProduct.map (fun _ : Fin n ↦ (c : k) • h.val.toLinearMap) =
        (c : k) ^ n • PiTensorProduct.map (fun _ : Fin n ↦ h.val.toLinearMap)
      simpa using
        (PiTensorProduct.mapMultilinear k (fun _ : Fin n ↦ E) (fun _ ↦ E)).map_smul_univ
          (fun _ ↦ (c : k)) (fun _ ↦ h.val.toLinearMap)
    rw [hmap]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)

/-- The actual group-algebra image of the SL tensor action is the selected
Schur--Weyl image algebra, for one fixed degree. This is the image-algebra
bridge for Bost p31; it includes degree zero and makes no general reductivity claim. -/
theorem tensorPowerSL_image_eq [CharZero k] (n : ℕ) :
    (tensorPowerSLRepresentation k E n).asAlgebraHom.range =
      auxiliaryEndomorphismAlgebra k E n := by
  apply Subalgebra.toSubmodule_injective
  rw [representation_range_eq_span, tensorPowerSL_span_eq_gl_span,
    span_range_piTensorProduct_map_eq_auxiliary]

/-- Each actual SL tensor power is semisimple as a group-algebra module.
This fixed-degree characteristic-zero result, including degree zero, is the
tensor-power producer for Bost p31. Polynomial and orbit-separation bridges
are separate; the group algebra itself is not asserted to be semisimple. -/
theorem tensorPowerSL_isSemisimpleModule [CharZero k] (n : ℕ) :
    IsSemisimpleModule (MonoidAlgebra k (SpecialLinearGroup k E))
      (tensorPowerSLRepresentation k E n).asModule := by
  have : IsSemisimpleRing (tensorPowerSLRepresentation k E n).asAlgebraHom.range := by
    rw [tensorPowerSL_image_eq]
    exact (associatedSubalgebras_semisimple k E n).2
  exact representation_isSemisimpleModule_of_image k (tensorPowerSLRepresentation k E n)

/-- Every invariant subspace of a fixed actual SL tensor power admits an
invariant complement, including degree zero. This is the representation form
of the Bost p31 tensor-power input, with the same remaining polynomial bridges. -/
theorem tensorPowerSL_isSemisimpleRepresentation [CharZero k] (n : ℕ) :
    Representation.IsSemisimpleRepresentation (tensorPowerSLRepresentation k E n) :=
  (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
    (tensorPowerSL_isSemisimpleModule k E n)

/-- An actual equivariant surjection from an invariant subspace of a fixed
SL tensor power has an equivariant linear section. This is the bounded
splitting input for Bost p31, without a general reductivity assertion. -/
theorem tensorPowerSL_submodule_surjection_splits [CharZero k] (n : ℕ)
    (U : Submodule (MonoidAlgebra k (SpecialLinearGroup k E))
      (tensorPowerSLRepresentation k E n).asModule)
    {Q : Type*} [AddCommGroup Q] [Module (MonoidAlgebra k (SpecialLinearGroup k E)) Q]
    (q : U →ₗ[MonoidAlgebra k (SpecialLinearGroup k E)] Q)
    (hq : Function.Surjective q) :
    ∃ s : Q →ₗ[MonoidAlgebra k (SpecialLinearGroup k E)] U,
      q ∘ₗ s = LinearMap.id := by
  have := tensorPowerSL_isSemisimpleModule k E n
  exact IsSemisimpleModule.lifting_property q hq LinearMap.id

/-- Every invariant of an equivariant quotient of an invariant subspace of an
actual SL tensor power has an invariant lift. Invariance is written using
the group basis elements of the actual group algebra. This is the individual
factor lift input for Bost p31; polynomial and two-factor bridges remain separate. -/
theorem tensorPowerSL_exists_invariant_lift [CharZero k] (n : ℕ)
    (U : Submodule (MonoidAlgebra k (SpecialLinearGroup k E))
      (tensorPowerSLRepresentation k E n).asModule)
    {Q : Type*} [AddCommGroup Q] [Module (MonoidAlgebra k (SpecialLinearGroup k E)) Q]
    (q : U →ₗ[MonoidAlgebra k (SpecialLinearGroup k E)] Q)
    (hq : Function.Surjective q) (y : Q)
    (hy : ∀ g : SpecialLinearGroup k E, MonoidAlgebra.single g (1 : k) • y = y) :
    ∃ x : U, q x = y ∧
      ∀ g : SpecialLinearGroup k E, MonoidAlgebra.single g (1 : k) • x = x := by
  obtain ⟨s, hs⟩ := tensorPowerSL_submodule_surjection_splits k E n U q hq
  refine ⟨s y, ?_, ?_⟩
  · exact DFunLike.congr_fun hs y
  · intro g
    rw [← s.map_smul, hy]

end ArakelovGeometry.InvariantTheory

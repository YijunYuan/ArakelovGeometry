/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

module

public import ExternalResults.EtingofRepresentationTheory.CentralizerDecomposition
public import ExternalResults.EtingofRepresentationTheory.TensorProducts.Auxiliary
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Data.Finite.Perm

/-!
# Selected tensor-power Schur--Weyl input

Selected from mathlib-initiative/EtingofRepresentationTheory, commit
752fe269b3233f08f0795aa4bcdc5b4c84be7a50; see provenance.json.
Only permutation centralizers and semisimplicity are retained;
detailed decompositions and Lie actions are omitted.
The application is the fixed-degree tensor-power input for Bost p31's binary
instability route. General reductivity, polynomial quotients, and orbit
separation are outside this module.
-/

@[expose] public section

open scoped TensorProduct

namespace RepresentationTheory.Auxiliary.MutualCentralizers

set_option backward.isDefEq.respectTransparency false

universe u v

variable (k : Type u) [Field k]
  (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- An auxiliary type associated with a field, a module, and a natural parameter. -/
abbrev auxiliarySpace := ⨂[k] (_ : Fin n), V

/-- The auxiliary space of a finite module is finite over the base field. -/
instance finite_auxiliarySpace : Module.Finite k (auxiliarySpace k V n) := by
  have : Module.Free k V := Module.Free.of_divisionRing k V
  let b := Module.Free.chooseBasis k V
  exact Module.Finite.of_basis (Basis.piTensorProduct (fun _ : Fin n => b))

/-- A permutation of a finite index type induces a linear self-equivalence of the auxiliary
space. -/
noncomputable def auxiliarySpacePermutationEquiv (σ : Equiv.Perm (Fin n)) :
    auxiliarySpace k V n ≃ₗ[k] auxiliarySpace k V n :=
  PiTensorProduct.reindex k (fun _ => V) σ

/-- The subalgebra of auxiliary-space endomorphisms associated with permutations. -/
noncomputable def permutationActionAlgebra :
    Subalgebra k (Module.End k (auxiliarySpace k V n)) :=
  Algebra.adjoin k (Set.range fun (σ : Equiv.Perm (Fin n)) =>
    (auxiliarySpacePermutationEquiv k V n σ).toLinearMap)

/-- An auxiliary subalgebra of endomorphisms of the auxiliary space. -/
noncomputable def auxiliaryEndomorphismAlgebra :
    Subalgebra k (Module.End k (auxiliarySpace k V n)) :=
  Algebra.adjoin k (Set.range fun (f : Module.End k V) =>
    PiTensorProduct.map (fun _ => f))

omit [Module.Finite k V] in
/-- The permutation equivalence commutes with the map induced by applying one linear
endomorphism factorwise. -/
theorem auxiliarySpacePermutationEquiv_comp_factorwiseMap
    (σ : Equiv.Perm (Fin n)) (f : Module.End k V) :
    (auxiliarySpacePermutationEquiv k V n σ).toLinearMap ∘ₗ PiTensorProduct.map (fun _ => f) =
    PiTensorProduct.map (fun _ => f) ∘ₗ (auxiliarySpacePermutationEquiv k V n σ).toLinearMap := by
  unfold auxiliarySpacePermutationEquiv
  apply LinearMap.ext
  intro x
  change (PiTensorProduct.reindex k (fun _ => V) σ) (PiTensorProduct.map (fun _ => f) x) =
    PiTensorProduct.map (fun _ => f) ((PiTensorProduct.reindex k (fun _ => V) σ) x)
  exact (PiTensorProduct.map_reindex (fun (_ : Fin n) => f) σ x).symm

omit [Module.Finite k V] in
/-- Every permutation-action endomorphism commutes with the auxiliary endomorphism algebra. -/
theorem permutationActionAlgebra_le_centralizer_auxiliaryEndomorphismAlgebra :
    permutationActionAlgebra k V n ≤ Subalgebra.centralizer k
      (auxiliaryEndomorphismAlgebra k V n :
        Set (Module.End k (auxiliarySpace k V n))) := by
  unfold permutationActionAlgebra
  apply Algebra.adjoin_le
  rintro x ⟨σ, rfl⟩
  simp only [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
  intro y hy
  unfold auxiliaryEndomorphismAlgebra at hy
  have hcomm : ∀ g ∈ Set.range (fun (f : Module.End k V) =>
      PiTensorProduct.map (R := k) (fun (_ : Fin n) => f)),
      Commute (↑(auxiliarySpacePermutationEquiv k V n σ) :
        Module.End k (auxiliarySpace k V n)) g := by
    rintro g ⟨f, rfl⟩
    exact auxiliarySpacePermutationEquiv_comp_factorwiseMap k V n σ f
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy hcomm).symm.eq

omit [Module.Finite k V] in
/-- Every element of the auxiliary endomorphism algebra commutes with the permutation-action
algebra. -/
theorem auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra :
    auxiliaryEndomorphismAlgebra k V n ≤ Subalgebra.centralizer k
      (permutationActionAlgebra k V n :
        Set (Module.End k (auxiliarySpace k V n))) := by
  rw [Subalgebra.le_centralizer_iff]
  exact permutationActionAlgebra_le_centralizer_auxiliaryEndomorphismAlgebra k V n

/-- Permutations define a monoid homomorphism into auxiliary-space endomorphisms. -/
noncomputable def permutationAction :
    Equiv.Perm (Fin n) →* Module.End k (auxiliarySpace k V n) where
  toFun σ := (auxiliarySpacePermutationEquiv k V n σ).toLinearMap
  map_one' := by
    simp only [auxiliarySpacePermutationEquiv]
    apply LinearMap.ext; intro x
    change (PiTensorProduct.reindex k (fun _ => V) (Equiv.refl _)) x = x
    simp [PiTensorProduct.reindex_refl]
  map_mul' σ τ := by
    simp only [auxiliarySpacePermutationEquiv]
    apply LinearMap.ext
    intro x
    change (PiTensorProduct.reindex k (fun _ => V) (σ * τ)) x =
      (PiTensorProduct.reindex k (fun _ => V) σ)
        ((PiTensorProduct.reindex k (fun _ => V) τ) x)
    rw [show (σ * τ : Equiv.Perm (Fin n)) = τ.trans σ from rfl,
      ← PiTensorProduct.reindex_reindex]

/-- The permutation action on the auxiliary space extends to an algebra homomorphism from the
permutation group algebra. -/
noncomputable def permutationGroupAlgebraAction :
    MonoidAlgebra k (Equiv.Perm (Fin n)) →ₐ[k] Module.End k (auxiliarySpace k V n) :=
  MonoidAlgebra.lift k (Module.End k (auxiliarySpace k V n)) (Equiv.Perm (Fin n))
    (permutationAction k V n)

omit [Module.Finite k V] in
/-- The range of the permutation group algebra action is the permutation-action subalgebra. -/
theorem range_permutationGroupAlgebraAction :
    (permutationGroupAlgebraAction k V n).range = permutationActionAlgebra k V n := by
  unfold permutationGroupAlgebraAction permutationActionAlgebra
  apply le_antisymm
  · rintro x ⟨f, rfl⟩
    induction f using MonoidAlgebra.induction_linear with
    | zero => exact Subalgebra.zero_mem _
    | add f g hf hg => rw [map_add]; exact Subalgebra.add_mem _ hf hg
    | single a b =>
      change (MonoidAlgebra.lift k _ _ (permutationAction k V n))
        (MonoidAlgebra.single a b) ∈ _
      rw [MonoidAlgebra.lift_single]
      exact Subalgebra.smul_mem _
        (Algebra.subset_adjoin (Set.mem_range.mpr ⟨a, by simp [permutationAction]⟩)) _
  · apply Algebra.adjoin_le
    rintro x ⟨σ, rfl⟩
    exact ⟨MonoidAlgebra.single σ 1, by
      simp [MonoidAlgebra.lift_single, permutationAction]⟩

/-- The permutation-action algebra is semisimple when the base field has characteristic zero. -/
instance permutationActionAlgebra_semisimple
    [CharZero k] :
    IsSemisimpleRing (permutationActionAlgebra k V n) := by
  rw [← range_permutationGroupAlgebraAction]
  have : NeZero (Nat.card (Equiv.Perm (Fin n)) : k) := by
    rw [Nat.card_perm, Nat.card_fin]
    exact ⟨Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)⟩
  exact (permutationGroupAlgebraAction k V n).toRingHom.rangeRestrict.isSemisimpleRing_of_surjective
    (permutationGroupAlgebraAction k V n).toRingHom.rangeRestrict_surjective

/-- The centralizer of the permutation-action algebra is the auxiliary endomorphism algebra. -/
theorem centralizer_permutationActionAlgebra
    [CharZero k] :
    Subalgebra.centralizer k
      (permutationActionAlgebra k V n :
        Set (Module.End k (auxiliarySpace k V n))) =
    auxiliaryEndomorphismAlgebra k V n := by
  apply le_antisymm
  · open TensorProducts.Auxiliary in
    intro φ hφ
    rw [Subalgebra.mem_centralizer_iff] at hφ
    change φ ∈ PiTensorProduct.Constructions.piTensorEndSubalgebraAlternate k V n
    have hconj : ∀ σ : Equiv.Perm (Fin n),
        (PiTensorProduct.reindex k (fun _ => V) σ).toLinearMap * φ *
        (PiTensorProduct.reindex k (fun _ => V) σ).symm.toLinearMap = φ := by
      intro σ
      set e := PiTensorProduct.reindex k (fun _ => V) σ
      have hcomm := hφ e.toLinearMap (Algebra.subset_adjoin ⟨σ, rfl⟩)
      have he_inv : e.toLinearMap * e.symm.toLinearMap = 1 := by
        ext v; simp [Module.End.mul_eq_comp]
      calc e.toLinearMap * φ * e.symm.toLinearMap
          = φ * e.toLinearMap * e.symm.toLinearMap := by rw [hcomm]
        _ = φ * (e.toLinearMap * e.symm.toLinearMap) := by rw [mul_assoc]
        _ = φ * 1 := by rw [he_inv]
        _ = φ := mul_one _
    set fullDiag := PiTensorProduct.Constructions.piTensorEndSubalgebraAlternate k V n
    have hfact : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hmem : φ ∈ Submodule.span k (Set.range fun f : Fin n → Module.End k V =>
        PiTensorProduct.map f) :=
      @span_range_map_eq_top k _ V _ _ n _ _ ▸ Submodule.mem_top
    have hsum := sum_reindexConjugates_mem_auxiliary (k := k) (V := V) (n := n) φ hmem
    have heq : ∑ σ : Equiv.Perm (Fin n),
        (PiTensorProduct.reindex k (fun _ => V) σ).toLinearMap * φ *
        (PiTensorProduct.reindex k (fun _ => V) σ).symm.toLinearMap =
        (n.factorial : k) • φ := by
      simp_rw [hconj, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul k]
    rw [heq] at hsum
    have := fullDiag.toSubmodule.smul_mem (n.factorial : k)⁻¹ hsum
    rwa [inv_smul_smul₀ hfact] at this
  · exact auxiliaryEndomorphismAlgebra_le_centralizer_permutationActionAlgebra
      k V n

/-- Both actual tensor endomorphism subalgebras are semisimple in characteristic zero.
This retained donor producer supplies the fixed-degree image algebra for Bost p31;
the detailed Schur--Weyl decomposition and general reductivity are not asserted. -/
theorem associatedSubalgebras_semisimple
    [CharZero k] :
    IsSemisimpleRing (permutationActionAlgebra k V n)
    ∧ IsSemisimpleRing (auxiliaryEndomorphismAlgebra k V n) := by
  constructor
  · exact permutationActionAlgebra_semisimple k V n
  · rw [← centralizer_permutationActionAlgebra
      k V n]
    have := permutationActionAlgebra_semisimple k V n
    exact CentralizerDecomposition.isSemisimpleRing_centralizer
      k (auxiliarySpace k V n) (permutationActionAlgebra k V n)


end RepresentationTheory.Auxiliary.MutualCentralizers

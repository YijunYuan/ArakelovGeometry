/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionIsomorphismSubspace
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionNativeSubquotientFiniteStage
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionQuotientEquiv

/-!
# Completed semilinear transport of actual restrictions and quotients
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
open AdelicStructure.ParameterSpaceExtension
variable {K L M E : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [AddCommGroup E] [Module K E]
  {S : AdelicStructure K}

/-- The actual completed fibre transport is semilinear over the canonical
isomorphism of the actual completed coefficient fields. -/
def completedScalarExtensionSemilinearEquiv (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
    ((pullbackAlgEquiv S σ x).abv.Completion ⊗[L] (L ⊗[K] E))
      ≃ₛₗ[((algEquivCompletedFields S σ x).toRingEquiv :
        (pullbackAlgEquiv S σ x).abv.Completion →+* x.abv.Completion)]
      (x.abv.Completion ⊗[M] (M ⊗[K] E)) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  letI := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  letI := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  refine { (completedScalarExtensionAlgEquiv (E := E) σ x).toAddEquiv with
    map_smul' := ?_ }
  intro a z
  change completedScalarExtensionAlgEquiv (E := E) σ x (a • z) =
    algEquivCompletedFields S σ x a • completedScalarExtensionAlgEquiv (E := E) σ x z
  induction z using TensorProduct.inductionOn with
  | tmul b z =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul,
      completedScalarExtensionAlgEquiv_rational, map_mul]
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]

/-- The completed ambient transport maps the literal completed image of every
actual extension-field subspace onto the completed image of its transport. -/
theorem completedScalarExtensionSemilinearEquiv_map_baseChange (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B : Submodule L (L ⊗[K] E)) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
    (B.baseChange (pullbackAlgEquiv S σ x).abv.Completion).map
      (completedScalarExtensionSemilinearEquiv (E := E) σ x).toLinearMap =
      (scalarExtensionSubspaceOrderIso (E := E) σ B).baseChange x.abv.Completion := by
  intro aL aM
  let := aL
  let := aM
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, Submodule.baseChange_eq_span, Submodule.span_le]
    rintro z ⟨b, hb, rfl⟩
    change completedScalarExtensionAlgEquiv (E := E) σ x (1 ⊗ₜ[L] b) ∈
      (scalarExtensionSubspaceOrderIso (E := E) σ B).baseChange x.abv.Completion
    rw [completedScalarExtensionAlgEquiv_rational, map_one]
    exact Submodule.tmul_mem_baseChange_of_mem _ ⟨b, hb, rfl⟩
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro z ⟨m, hm, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hm
    refine ⟨1 ⊗ₜ[L] b, Submodule.tmul_mem_baseChange_of_mem _ hb, ?_⟩
    change completedScalarExtensionAlgEquiv (E := E) σ x (1 ⊗ₜ[L] b) = _
    simp only [completedScalarExtensionAlgEquiv_rational, map_one]
    rfl

/-- Canonical semilinear transport of the actual tensor fibres of a subspace,
obtained from the actual completed inclusions and ambient transport. -/
def completedScalarExtensionRestrictionEquiv (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B : Submodule L (L ⊗[K] E)) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
    ((pullbackAlgEquiv S σ x).abv.Completion ⊗[L] B)
      ≃ₛₗ[((algEquivCompletedFields S σ x).toRingEquiv :
        (pullbackAlgEquiv S σ x).abv.Completion →+* x.abv.Completion)]
      (x.abv.Completion ⊗[M] scalarExtensionSubspaceOrderIso (E := E) σ B) := by
  intro aL aM
  let := aL
  let := aM
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  let : Module.Free L (pullbackAlgEquiv S σ x).abv.Completion :=
    Module.Free.of_divisionRing L _
  let : Module.Flat L (pullbackAlgEquiv S σ x).abv.Completion := Module.Flat.of_free
  let : Module.Free M x.abv.Completion := Module.Free.of_divisionRing M _
  let : Module.Flat M x.abv.Completion := Module.Flat.of_free
  exact (Submodule.toBaseChange.toLinearEquiv
    (pullbackAlgEquiv S σ x).abv.Completion B).trans
    (((completedScalarExtensionSemilinearEquiv (E := E) σ x).ofSubmodules _ _
      (completedScalarExtensionSemilinearEquiv_map_baseChange σ x B)).trans
      (Submodule.toBaseChange.toLinearEquiv x.abv.Completion
        (scalarExtensionSubspaceOrderIso (E := E) σ B)).symm)

/-- Completed restriction transport intertwines the literal completed inclusions. -/
theorem completedScalarExtensionRestrictionEquiv_inclusion (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B : Submodule L (L ⊗[K] E))
    (z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L] B) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype.baseChange x.abv.Completion
      (completedScalarExtensionRestrictionEquiv σ x B z) =
      completedScalarExtensionAlgEquiv (E := E) σ x
        (B.subtype.baseChange (pullbackAlgEquiv S σ x).abv.Completion z) := by
  intro aL aM
  let := aL
  let := aM
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  let : Module.Free L (pullbackAlgEquiv S σ x).abv.Completion :=
    Module.Free.of_divisionRing L _
  let : Module.Flat L (pullbackAlgEquiv S σ x).abv.Completion := Module.Flat.of_free
  let : Module.Free M x.abv.Completion := Module.Free.of_divisionRing M _
  let : Module.Flat M x.abv.Completion := Module.Flat.of_free
  change ((Submodule.toBaseChange.toLinearEquiv x.abv.Completion
    (scalarExtensionSubspaceOrderIso (E := E) σ B))
      ((Submodule.toBaseChange.toLinearEquiv x.abv.Completion
        (scalarExtensionSubspaceOrderIso (E := E) σ B)).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- On every completed coefficient, restriction transport is the completion
of the prescribed rational semilinear subspace map. -/
theorem completedScalarExtensionRestrictionEquiv_tmul (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B : Submodule L (L ⊗[K] E))
    (a : (pullbackAlgEquiv S σ x).abv.Completion) (b : B) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    completedScalarExtensionRestrictionEquiv σ x B (a ⊗ₜ[L] b) =
      algEquivCompletedFields S σ x a ⊗ₜ[M] scalarExtensionSubspaceSemilinearEquiv σ B b := by
  intro aL aM
  let := aL
  let := aM
  let : Module.Free M x.abv.Completion := Module.Free.of_divisionRing M _
  let : Module.Flat M x.abv.Completion := Module.Flat.of_free
  have hi : Function.Injective
      ((scalarExtensionSubspaceOrderIso (E := E) σ B).subtype.baseChange x.abv.Completion) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.subtype_injective _)
  apply hi
  rw [completedScalarExtensionRestrictionEquiv_inclusion]
  simp only [LinearMap.baseChange_tmul, completedScalarExtensionAlgEquiv_rational]
  rfl

/-- The completed actual subquotient kernel has exactly the transported image. -/
theorem completedScalarExtensionRestrictionEquiv_map_kernel (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
    ((T.comap B.subtype).baseChange (pullbackAlgEquiv S σ x).abv.Completion).map
      (completedScalarExtensionRestrictionEquiv σ x B).toLinearMap =
      (((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype).baseChange x.abv.Completion) := by
  intro aL aM
  let := aL
  let := aM
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  let : Module.Free M x.abv.Completion := Module.Free.of_divisionRing M _
  let : Module.Flat M x.abv.Completion := Module.Flat.of_free
  let e := completedScalarExtensionRestrictionEquiv σ x B
  let c := completedScalarExtensionSemilinearEquiv (E := E) σ x
  let D := scalarExtensionSubspaceOrderIso (E := E) σ B
  have hc : (D.subtype.baseChange x.abv.Completion).comp e.toLinearMap =
      c.toLinearMap.comp (B.subtype.baseChange (pullbackAlgEquiv S σ x).abv.Completion) := by
    ext z
    exact completedScalarExtensionRestrictionEquiv_inclusion σ x B z
  have hi : Function.Injective (D.subtype.baseChange x.abv.Completion) :=
    Module.Flat.lTensor_preserves_injective_linearMap D.subtype D.subtype_injective
  apply Submodule.map_injective_of_injective hi
  rw [← Submodule.map_comp, hc, Submodule.map_comp,
    map_baseChange_comap_subtype T B hTB,
    completedScalarExtensionSemilinearEquiv_map_baseChange]
  exact (map_baseChange_comap_subtype
    (scalarExtensionSubspaceOrderIso (E := E) σ T) D
    ((scalarExtensionSubspaceOrderIso (E := E) σ).monotone hTB)).symm

/-- The canonical coefficient ring equivalence, with its base-completion
algebra instances confined to the construction. -/
abbrev completedScalarExtensionCoefficientRingEquiv (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M) :
    (pullbackAlgEquiv S σ x).abv.Completion ≃+* x.abv.Completion := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  exact (algEquivCompletedFields S σ x).toRingEquiv

/-- Canonical transport on the literal completed tensor fibres of native
subquotients, through tensor quotient equivalences and the produced kernel image. -/
def completedScalarExtensionSubquotientEquiv (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B) :
    letI := RingHomInvPair.of_ringEquiv (completedScalarExtensionCoefficientRingEquiv σ x)
    letI := RingHomInvPair.of_ringEquiv_symm (completedScalarExtensionCoefficientRingEquiv σ x)
    ((pullbackAlgEquiv S σ x).abv.Completion ⊗[L] (B ⧸ T.comap B.subtype))
      ≃ₛₗ[((completedScalarExtensionCoefficientRingEquiv σ x) :
        (pullbackAlgEquiv S σ x).abv.Completion →+* x.abv.Completion)]
      (x.abv.Completion ⊗[M] (scalarExtensionSubspaceOrderIso (E := E) σ B ⧸
        (scalarExtensionSubspaceOrderIso (E := E) σ T).comap
          (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  let dL := tensorQuotientBaseChangeEquiv
    (L := (pullbackAlgEquiv S σ x).abv.Completion) (T.comap B.subtype)
  let dM := tensorQuotientBaseChangeEquiv (L := x.abv.Completion)
    ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
      (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)
  let q := Submodule.Quotient.equiv _ _ (completedScalarExtensionRestrictionEquiv σ x B)
    (completedScalarExtensionRestrictionEquiv_map_kernel σ x B T hTB)
  exact (dL.trans q).trans dM.symm

/-- The produced completed native subquotient map commutes with every actual
completed quotient-map value, not only with rational representatives. -/
theorem completedScalarExtensionSubquotientEquiv_mkQ (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B)
    (z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L] B) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    completedScalarExtensionSubquotientEquiv σ x B T hTB
      ((T.comap B.subtype).mkQ.baseChange (pullbackAlgEquiv S σ x).abv.Completion z) =
      ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype).mkQ.baseChange x.abv.Completion
          (completedScalarExtensionRestrictionEquiv σ x B z) := by
  intro aL aM
  let := aL
  let := aM
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  let P := T.comap B.subtype
  let Q := (scalarExtensionSubspaceOrderIso (E := E) σ T).comap
    (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype
  let e := completedScalarExtensionRestrictionEquiv σ x B
  let dL := tensorQuotientBaseChangeEquiv (L := (pullbackAlgEquiv S σ x).abv.Completion) P
  let dM := tensorQuotientBaseChangeEquiv (L := x.abv.Completion) Q
  let q := Submodule.Quotient.equiv _ _ e
    (completedScalarExtensionRestrictionEquiv_map_kernel σ x B T hTB)
  have hL : dL (P.mkQ.baseChange (pullbackAlgEquiv S σ x).abv.Completion z) =
      Submodule.Quotient.mk z := congrArg (fun f : _ →ₗ[_] _ => f z)
        (tensorQuotientBaseChangeEquiv_comp_mkQ
          (L := (pullbackAlgEquiv S σ x).abv.Completion) P)
  have hM : dM (Q.mkQ.baseChange x.abv.Completion (e z)) =
      Submodule.Quotient.mk (e z) := congrArg (fun f : _ →ₗ[_] _ => f (e z))
        (tensorQuotientBaseChangeEquiv_comp_mkQ (L := x.abv.Completion) Q)
  change dM.symm (q (dL (P.mkQ.baseChange (pullbackAlgEquiv S σ x).abv.Completion z))) = _
  apply dM.injective
  rw [LinearEquiv.apply_symm_apply, hL, hM]
  rfl

/-- Native subquotient transport is the completion of the actual prescribed
rational quotient map, on every completed coefficient and every native class. -/
theorem completedScalarExtensionSubquotientEquiv_tmul (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B)
    (a : (pullbackAlgEquiv S σ x).abv.Completion) (b : B ⧸ T.comap B.subtype) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    completedScalarExtensionSubquotientEquiv σ x B T hTB (a ⊗ₜ[L] b) =
      algEquivCompletedFields S σ x a ⊗ₜ[M] scalarExtensionSubquotientSemilinearEquiv σ B T b := by
  intro aL aM
  let := aL
  let := aM
  induction b using Submodule.Quotient.induction_on with
  | _ b =>
    change completedScalarExtensionSubquotientEquiv σ x B T hTB
      ((T.comap B.subtype).mkQ.baseChange (pullbackAlgEquiv S σ x).abv.Completion
        (a ⊗ₜ[L] b)) = _
    rw [completedScalarExtensionSubquotientEquiv_mkQ,
      completedScalarExtensionRestrictionEquiv_tmul, LinearMap.baseChange_tmul]
    rfl

namespace NormFamily
variable [FiniteDimensional K E] [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]

/-- Actual restricted scalar-extension norms agree on every completed vector. -/
theorem scalarExtension_restrict_norm_algEquiv (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B : Submodule L (L ⊗[K] E))
    (z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L] B) :
    ((ξ.scalarExtension (L := M)).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ B)).norm x
        (completedScalarExtensionRestrictionEquiv σ x B z) =
      ((ξ.scalarExtension (L := L)).restrict B).norm (pullbackAlgEquiv S σ x) z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  change (ξ.scalarExtension (L := M)).norm x
    ((scalarExtensionSubspaceOrderIso (E := E) σ B).subtype.baseChange x.abv.Completion
      (completedScalarExtensionRestrictionEquiv σ x B z)) =
    (ξ.scalarExtension (L := L)).norm (pullbackAlgEquiv S σ x)
      (B.subtype.baseChange (pullbackAlgEquiv S σ x).abv.Completion z)
  rw [completedScalarExtensionRestrictionEquiv_inclusion]
  exact ξ.scalarExtension_norm_algEquiv σ x _

/-- Every completed vector in every actual native subquotient preserves its
quotient norm under the produced field-isomorphism transport. -/
theorem scalarExtension_subquotient_norm_algEquiv (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B)
    (z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L] (B ⧸ T.comap B.subtype)) :
    (((ξ.scalarExtension (L := M)).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ B)).quotient
        ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
          (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)).norm x
            (completedScalarExtensionSubquotientEquiv σ x B T hTB z) =
      (((ξ.scalarExtension (L := L)).restrict B).quotient (T.comap B.subtype)).norm
        (pullbackAlgEquiv S σ x) z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  let η := (ξ.scalarExtension (L := L)).restrict B
  let θ := (ξ.scalarExtension (L := M)).restrict
    (scalarExtensionSubspaceOrderIso (E := E) σ B)
  let P := T.comap B.subtype
  let Q := (scalarExtensionSubspaceOrderIso (E := E) σ T).comap
    (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype
  let y : (S.algebraicExtension L).Ω := pullbackAlgEquiv S σ x
  let w : (S.algebraicExtension M).Ω := x
  let e := completedScalarExtensionRestrictionEquiv σ x B
  let q := completedScalarExtensionSubquotientEquiv σ x B T hTB
  change θ.quotientSeminorm Q.mkQ Q.mkQ_surjective w (q z) =
    η.quotientSeminorm P.mkQ P.mkQ_surjective y z
  apply le_antisymm
  · apply (η.le_quotientSeminorm_iff P.mkQ P.mkQ_surjective y z _).2
    intro u hu
    have hq : Q.mkQ.baseChange x.abv.Completion (e u) = q z := by
      rw [← hu]
      exact (completedScalarExtensionSubquotientEquiv_mkQ σ x B T hTB u).symm
    calc
      θ.quotientSeminorm Q.mkQ Q.mkQ_surjective w (q z) ≤ θ.norm w (e u) := by
        rw [← hq]
        exact θ.quotientSeminorm_le Q.mkQ Q.mkQ_surjective w (e u)
      _ = η.norm y u := ξ.scalarExtension_restrict_norm_algEquiv σ x B u
  · apply (θ.le_quotientSeminorm_iff Q.mkQ Q.mkQ_surjective w (q z) _).2
    intro v hv
    obtain ⟨u, rfl⟩ := e.surjective v
    have hu : P.mkQ.baseChange (pullbackAlgEquiv S σ x).abv.Completion u = z := by
      apply q.injective
      exact (completedScalarExtensionSubquotientEquiv_mkQ σ x B T hTB u).trans hv
    calc
      η.quotientSeminorm P.mkQ P.mkQ_surjective y z ≤ η.norm y u := by
        rw [← hu]
        exact η.quotientSeminorm_le P.mkQ P.mkQ_surjective y u
      _ = θ.norm w (e u) := (ξ.scalarExtension_restrict_norm_algEquiv σ x B u).symm

end NormFamily
end ArakelovGeometry

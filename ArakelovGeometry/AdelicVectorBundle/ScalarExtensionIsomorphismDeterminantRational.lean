/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionIsomorphismDeterminant

/-!
# Rational determinant transport under scalar-field isomorphisms
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

section RationalDeterminant
variable {L M U V : Type*} [Field L] [Field M]
  [AddCommGroup U] [AddCommGroup V] [Module L U] [Module M V]
  (σ : L ≃+* M)

local instance : RingHomInvPair (σ : L →+* M) (σ.symm : M →+* L) :=
  RingHomInvPair.of_ringEquiv σ
local instance : RingHomInvPair (σ.symm : M →+* L) (σ : L →+* M) :=
  RingHomInvPair.of_ringEquiv_symm σ

/-- The rational determinant map of a semilinear equivalence, through the
canonical exterior map and the equality of top degrees. -/
def determinantSemilinearEquiv (f : U ≃ₛₗ[(σ : L →+* M)] V)
    (hr : Module.finrank L U = Module.finrank M V) :
    (⋀[L]^(Module.finrank L U) U) ≃ₛₗ[(σ : L →+* M)]
      (⋀[M]^(Module.finrank M V) V) :=
  (exteriorPowerSemilinearEquiv σ f (Module.finrank L U)).trans
    (exteriorPowerDegreeEquiv M V hr)

/-- The rational determinant map has the canonical formula on every wedge. -/
theorem determinantSemilinearEquiv_ιMulti (f : U ≃ₛₗ[(σ : L →+* M)] V)
    (hr : Module.finrank L U = Module.finrank M V)
    (v : Fin (Module.finrank L U) → U) :
    determinantSemilinearEquiv σ f hr (_root_.exteriorPower.ιMulti L
      (Module.finrank L U) v) =
      _root_.exteriorPower.ιMulti M (Module.finrank M V)
        (fun i ↦ f (v ((finCongr hr).symm i))) := by
  change exteriorPowerDegreeEquiv M V hr
    (exteriorPowerSemilinearEquiv σ f (Module.finrank L U)
      (_root_.exteriorPower.ιMulti L (Module.finrank L U) v)) = _
  rw [exteriorPowerSemilinearEquiv_ιMulti, exteriorPowerDegreeEquiv_ιMulti]

variable {A C : Type*} [Field A] [Field C] [Algebra L A] [Algebra M C]
  (τ : A ≃+* C)

local instance : RingHomInvPair (τ : A →+* C) (τ.symm : C →+* A) :=
  RingHomInvPair.of_ringEquiv τ
local instance : RingHomInvPair (τ.symm : C →+* A) (τ : A →+* C) :=
  RingHomInvPair.of_ringEquiv_symm τ

/-- Exterior base change intertwines the produced rational and completed
determinant maps on every scalar tensor, including the empty wedge. -/
theorem completedDeterminantSemilinearEquiv_tmul
    (f : U ≃ₛₗ[(σ : L →+* M)] V)
    (e : (A ⊗[L] U) ≃ₛₗ[(τ : A →+* C)] (C ⊗[M] V))
    (hr : Module.finrank L U = Module.finrank M V)
    (hτ : ∀ b, τ (algebraMap L A b) = algebraMap M C (σ b))
    (he : ∀ a u, e (a ⊗ₜ[L] u) = τ a ⊗ₜ[M] f u)
    (a : A) (z : ⋀[L]^(Module.finrank L U) U) :
    completedDeterminantSemilinearEquiv τ e hr (a ⊗ₜ[L] z) =
      τ a ⊗ₜ[M] determinantSemilinearEquiv σ f hr z := by
  let d := completedDeterminantSemilinearEquiv τ e hr
  have hz : z ∈ Submodule.span L
      (Set.range (_root_.exteriorPower.ιMulti L (Module.finrank L U))) := by
    rw [_root_.exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  have h : ∀ a : A, d (a ⊗ₜ[L] z) =
      τ a ⊗ₜ[M] determinantSemilinearEquiv σ f hr z := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      have h1 : d (1 ⊗ₜ[L] _root_.exteriorPower.ιMulti L (Module.finrank L U) v) =
          1 ⊗ₜ[M] determinantSemilinearEquiv σ f hr
            (_root_.exteriorPower.ιMulti L (Module.finrank L U) v) := by
        have hs := exteriorBaseChangeEquiv_symm_ιMulti_tmul L A U
          (Module.finrank L U) (fun _ ↦ 1) v
        simp only [Finset.prod_const_one] at hs
        rw [← hs]
        change completedDeterminantSemilinearEquiv τ e hr _ = _
        rw [completedDeterminantSemilinearEquiv_ιMulti,
          determinantSemilinearEquiv_ιMulti]
        simpa only [he, map_one, Finset.prod_const_one] using
          exteriorBaseChangeEquiv_symm_ιMulti_tmul M C V
            (Module.finrank M V) (fun _ ↦ 1)
              (fun i ↦ f (v ((finCongr hr).symm i)))
      intro a
      calc
        d (a ⊗ₜ[L] _root_.exteriorPower.ιMulti L (Module.finrank L U) v) =
            d (a • (1 ⊗ₜ[L] _root_.exteriorPower.ιMulti L (Module.finrank L U) v)) := by
          simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        _ = τ a ⊗ₜ[M] determinantSemilinearEquiv σ f hr
            (_root_.exteriorPower.ιMulti L (Module.finrank L U) v) := by
          rw [d.map_smulₛₗ, h1]
          simp only [RingEquiv.coe_toRingHom, TensorProduct.smul_tmul',
            smul_eq_mul, mul_one]
    | zero => intro a; simp only [TensorProduct.tmul_zero, map_zero]
    | add z w hz hw ihz ihw =>
      intro a
      simp only [TensorProduct.tmul_add, map_add, ihz, ihw]
    | smul b z hz ih =>
      intro a
      rw [← TensorProduct.smul_tmul, ih,
        (determinantSemilinearEquiv σ f hr).map_smulₛₗ, ← TensorProduct.smul_tmul]
      simp only [Algebra.smul_def, map_mul, hτ, RingEquiv.coe_toRingHom]
  exact h a

end RationalDeterminant

section ScalarExtensionSubquotient
open AdelicStructure.ParameterSpaceExtension
variable {K L M E : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {S : AdelicStructure K}

/-- The actual rational determinant equivalence of native subquotients,
using their produced semilinear map and equality of dimensions. -/
def scalarExtensionSubquotientDeterminantEquiv (σ : L ≃ₐ[K] M)
    (B T : Submodule L (L ⊗[K] E)) :
    letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
    let Q := B ⧸ T.comap B.subtype
    let Q' := scalarExtensionSubspaceOrderIso (E := E) σ B ⧸
      (scalarExtensionSubspaceOrderIso (E := E) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype
    (⋀[L]^(Module.finrank L Q) Q) ≃ₛₗ[(σ.toRingEquiv : L →+* M)]
      (⋀[M]^(Module.finrank M Q') Q') := by
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  exact determinantSemilinearEquiv σ.toRingEquiv
    (scalarExtensionSubquotientSemilinearEquiv σ B T)
    (scalarExtensionSubquotientSemilinearEquiv_finrank σ B T).symm

/-- The actual completed determinant map is the completion of the prescribed
rational determinant map on every coefficient and every rational vector. -/
theorem completedScalarExtensionSubquotientDeterminantEquiv_tmul
    (σ : L ≃ₐ[K] M) (x : AdelicStructure.ParameterSpaceExtension S M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B)
    (a : (pullbackAlgEquiv S σ x).abv.Completion)
    (z : ⋀[L]^(Module.finrank L (B ⧸ T.comap B.subtype)) (B ⧸ T.comap B.subtype)) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    completedScalarExtensionSubquotientDeterminantEquiv σ x B T hTB (a ⊗ₜ[L] z) =
      algEquivCompletedFields S σ x a ⊗ₜ[M]
        scalarExtensionSubquotientDeterminantEquiv σ B T z := by
  intro aL aM
  let := aL
  let := aM
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  exact completedDeterminantSemilinearEquiv_tmul σ.toRingEquiv
    (algEquivCompletedFields S σ x).toRingEquiv
    (scalarExtensionSubquotientSemilinearEquiv σ B T)
    (completedScalarExtensionSubquotientEquiv σ x B T hTB)
    (scalarExtensionSubquotientSemilinearEquiv_finrank σ B T).symm
    (algEquivCompletedFields_algebraMap S σ x)
    (completedScalarExtensionSubquotientEquiv_tmul σ x B T hTB) a z

namespace NormFamily
variable [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]

/-- The norms of literal rational determinant images agree at every place
and on every completed coefficient. -/
theorem scalarExtension_subquotient_determinant_norm_tmul_algEquiv
    (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B)
    (a : (pullbackAlgEquiv S σ x).abv.Completion)
    (z : ⋀[L]^(Module.finrank L (B ⧸ T.comap B.subtype)) (B ⧸ T.comap B.subtype)) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    (((ξ.scalarExtension (L := M)).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ B)).quotient
        ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
          (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)).determinant.norm x
            (algEquivCompletedFields S σ x a ⊗ₜ[M]
              scalarExtensionSubquotientDeterminantEquiv σ B T z) =
      (((ξ.scalarExtension (L := L)).restrict B).quotient
        (T.comap B.subtype)).determinant.norm (pullbackAlgEquiv S σ x) (a ⊗ₜ[L] z) := by
  intro aL aM
  let := aL
  let := aM
  let Q' := scalarExtensionSubspaceOrderIso (E := E) σ B ⧸
    (scalarExtensionSubspaceOrderIso (E := E) σ T).comap
      (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype
  let p : (x.abv.Completion ⊗[M] (⋀[M]^(Module.finrank M Q') Q')) → ℝ :=
    (((ξ.scalarExtension (L := M)).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ B)).quotient
        ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
          (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)).determinant.norm x
  have hm := completedScalarExtensionSubquotientDeterminantEquiv_tmul
    σ x B T hTB a z
  exact (congrArg p hm).symm.trans
    (ξ.scalarExtension_subquotient_determinant_norm_algEquiv
      σ x B T hTB (a ⊗ₜ[L] z))

/-- The literal rational determinant logarithm profile is pulled back by
the actual place map. The formula also uses the total real logarithm at zero. -/
theorem scalarExtension_subquotient_determinant_log_norm_algEquiv
    (ξ : NormFamily S E) (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B)
    (z : ⋀[L]^(Module.finrank L (B ⧸ T.comap B.subtype)) (B ⧸ T.comap B.subtype)) :
    Real.log ((((ξ.scalarExtension (L := M)).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ B)).quotient
        ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
          (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)).determinant.norm x
            (1 ⊗ₜ[M] scalarExtensionSubquotientDeterminantEquiv σ B T z)) =
      Real.log ((((ξ.scalarExtension (L := L)).restrict B).quotient
        (T.comap B.subtype)).determinant.norm (pullbackAlgEquiv S σ x) (1 ⊗ₜ[L] z)) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  have h := ξ.scalarExtension_subquotient_determinant_norm_tmul_algEquiv
    σ x B T hTB 1 z
  simp only [map_one] at h
  exact congrArg Real.log h

end NormFamily
end ScalarExtensionSubquotient
end ArakelovGeometry

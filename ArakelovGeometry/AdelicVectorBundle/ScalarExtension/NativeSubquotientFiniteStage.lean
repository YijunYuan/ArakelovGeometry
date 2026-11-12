/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.QuotientEquiv

import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.ComplexQuotient
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.FiniteStage.RestrictionIsometry
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Subspace.ComplexDescent
import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual finite-stage native subquotient isometries

Simultaneous descent of two nested subspaces preserves the genuine quotient
kernel under the canonical subspace tensor map. The tensor quotient and
quotient-image equivalences then identify the actual native subquotient with
an extended finite-stage subquotient, on every completed normed fibre.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
universe u v w wE

section SubmoduleBaseChange
variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
  {E : Type*} [AddCommGroup E] [Module K E]

/-- Nested-subspace kernels have their actual base-changed image under the
scalar-extended ambient subtype map. No dimension certificate is required. -/
theorem map_baseChange_comap_subtype (P Q : Submodule K E) (hPQ : P ≤ Q) :
    ((P.comap Q.subtype).baseChange L).map (Q.subtype.baseChange L) = P.baseChange L := by
  let C := P.comap Q.subtype
  let e := Submodule.comapSubtypeEquivOfLe hPQ
  have hc : Q.subtype.comp C.subtype = P.subtype.comp e.toLinearMap := by
    ext x
    rfl
  change (C.subtype.baseChange L).range.map (Q.subtype.baseChange L) =
    (P.subtype.baseChange L).range
  rw [← LinearMap.range_comp, ← LinearMap.baseChange_comp, hc,
    LinearMap.baseChange_comp]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.2 (LinearMap.baseChange_surjective L e.surjective))

end SubmoduleBaseChange

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]
  {E : Type wE} [AddCommGroup E] [Module K E]

/-- The actual canonical restricted tower-cancellation equivalence. -/
def finiteStageRestrictionEquiv (F : Type*) [Field F] [Algebra K F] [Algebra F L]
    [IsScalarTower K F L]
    (B : Submodule F (F ⊗[K] E)) :
    (L ⊗[F] B) ≃ₗ[L]
      ((B.baseChange L).map
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap) :=
  (Submodule.toBaseChange.toLinearEquiv L B).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).submoduleMap
      (B.baseChange L))

/-- The actual nested finite-stage kernel maps to exactly the native target
kernel under the canonical restricted tower cancellation map. -/
theorem finiteStageRestrictionEquiv_map_subquotient_kernel
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (P.baseChange L).map c.toLinearMap
    let B := (Q.baseChange L).map c.toLinearMap
    ((P.comap Q.subtype).baseChange L).map
      (finiteStageRestrictionEquiv (L := L) F Q).toLinearMap = A.comap B.subtype := by
  intro c A B
  let e := finiteStageRestrictionEquiv (L := L) F Q
  have hc : B.subtype.comp e.toLinearMap = c.toLinearMap.comp (Q.subtype.baseChange L) := by
    rfl
  apply Submodule.map_injective_of_injective B.subtype_injective
  rw [← Submodule.map_comp, hc, Submodule.map_comp, map_baseChange_comap_subtype P Q hPQ,
    Submodule.map_comap_subtype]
  exact (inf_eq_right.mpr
    (Submodule.map_mono (Submodule.baseChange_mono (A := L) hPQ))).symm

/-- The canonical tensor quotient followed by actual quotient-image tower
cancellation identifies the genuine extended finite-stage subquotient. -/
def finiteStageSubquotientEquiv
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q) :
    (L ⊗[F] (Q ⧸ P.comap Q.subtype)) ≃ₗ[L]
      (((Q.baseChange L).map
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap) ⧸
        (((P.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap).comap
          ((Q.baseChange L).map
            (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap).subtype)) :=
  (tensorQuotientBaseChangeEquiv (L := L) (P.comap Q.subtype)).trans
    (Submodule.Quotient.equiv _ _ (finiteStageRestrictionEquiv (L := L) F Q)
      (finiteStageRestrictionEquiv_map_subquotient_kernel (L := L) F P Q hPQ))


namespace NormFamily

section QuotientTransport
variable {k : Type*} [Field k] {l : Type*} [Field l] [Algebra k l]
  [Algebra.IsAlgebraic k l] {T : AdelicStructure k}
  {X : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]

private theorem nativeStage_tensorQuotient_norm_eq (ξ : NormFamily T X)
    [hN : T.IsArchimedeanNormalized]
    (hi : ∃ a : k, a ^ 2 = -1) (P : Submodule k X)
    (x : T.ParameterSpaceExtension l) (z : x.abv.Completion ⊗[l] (l ⊗[k] (X ⧸ P))) :
    ((ξ.scalarExtension (L := l)).quotient (P.baseChange l)).norm x
      ((tensorQuotientBaseChangeEquiv (L := l) P).toLinearMap.baseChange x.abv.Completion z) =
      ((ξ.quotient P).scalarExtension (L := l)).norm x z := by
  let e := tensorQuotientBaseChangeEquiv (L := l) P
  let η := ξ.scalarExtension (L := l)
  let ω : (T.algebraicExtension l).Ω := x
  change ((T.algebraicExtension l).ϕ ω).Completion ⊗[l] (l ⊗[k] (X ⧸ P)) at z
  have hc := η.pushforward_comp_norm (P.mkQ.baseChange l)
    (LinearMap.baseChange_surjective l P.mkQ_surjective) e.toLinearMap e.surjective ω
      (e.toLinearMap.baseChange ((T.algebraicExtension l).ϕ ω).Completion z)
  dsimp only [e] at hc
  simp only [tensorQuotientBaseChangeEquiv_comp_mkQ] at hc
  have ht := (η.pushforward (P.mkQ.baseChange l)
    (LinearMap.baseChange_surjective l P.mkQ_surjective)).pushforward_norm_of_injective
    e.toLinearMap e.surjective e.injective ω z
  exact (hc.symm.trans ht).trans
    (ξ.scalarExtension_pushforward_norm_eq_of_sqrt_neg_one hi P.mkQ P.mkQ_surjective x z)

end QuotientTransport

section QuotientIsometry
variable {k : Type*} [Field k] {T : AdelicStructure k}
  {X Y : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
  [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]

private theorem nativeStage_quotientEquiv_norm_eq_of_map_eq
    (ξ : NormFamily T X) (η : NormFamily T Y) (ω : T.Ω) (e : X ≃ₗ[k] Y)
    (P : Submodule k X) (Q : Submodule k Y) (hQ : P.map e.toLinearMap = Q)
    (he : ∀ t, η.norm ω (e.toLinearMap.baseChange (T.ϕ ω).Completion t) = ξ.norm ω t)
    (z : (T.ϕ ω).Completion ⊗[k] (X ⧸ P)) :
    (η.quotient Q).norm ω
      ((Submodule.Quotient.equiv P Q e hQ).toLinearMap.baseChange (T.ϕ ω).Completion z) =
      (ξ.quotient P).norm ω z := by
  subst Q
  have h := quotientEquiv_norm_eq ξ η ω e P he z
  dsimp only at h
  exact h

end QuotientIsometry

variable {S : AdelicStructure.{u, v} K} [Algebra.IsAlgebraic K L]

private theorem nativeStage_quotient_tower_norm_eq
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L]
    {X Y : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    [AddCommGroup Y] [Module L Y] [FiniteDimensional L Y]
    (η : NormFamily ((S.algebraicExtension F).algebraicExtension L) X)
    (θ : NormFamily (S.algebraicExtension L) Y) (e : X ≃ₗ[L] Y)
    (P : Submodule L X) (Q : Submodule L Y) (hQ : P.map e.toLinearMap = Q)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (he : ∀ t, θ.norm (scalarExtensionTowerPlace x)
      (e.toLinearMap.baseChange x.abv.Completion t) = η.norm x t)
    (z : x.abv.Completion ⊗[L] (X ⧸ P)) :
    (θ.quotient Q).norm (scalarExtensionTowerPlace x)
      ((Submodule.Quotient.equiv P Q e hQ).toLinearMap.baseChange x.abv.Completion z) =
      (η.quotient P).norm x z := by
  let θ' : NormFamily ((S.algebraicExtension F).algebraicExtension L) Y :=
    { norm x := θ.norm (scalarExtensionTowerPlace x)
      norm_eq_zero_iff x := θ.norm_eq_zero_iff (scalarExtensionTowerPlace x) }
  exact nativeStage_quotientEquiv_norm_eq_of_map_eq η θ' x e P Q hQ he z

variable [FiniteDimensional K E]

/-- The canonical actual native subquotient equivalence preserves every
completed norm under the actual tower place map. Normalization and the true
finite-stage square root are explicit; original ultrametricity is unnecessary. -/
theorem scalarExtension_subquotient_finiteStage_norm_eq (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] (hi : ∃ a : F, a ^ 2 = -1)
    (P Q : Submodule F (F ⊗[K] E)) (hPQ : P ≤ Q)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
    (z : x.abv.Completion ⊗[L] (L ⊗[F] (Q ⧸ P.comap Q.subtype))) :
    let c := TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E
    let A := (P.baseChange L).map c.toLinearMap
    let B := (Q.baseChange L).map c.toLinearMap
    (((ξ.scalarExtension (L := L)).restrict B).quotient (A.comap B.subtype)).norm
      (scalarExtensionTowerPlace x)
      ((finiteStageSubquotientEquiv (L := L) F P Q hPQ).toLinearMap.baseChange x.abv.Completion z) =
      ((((ξ.scalarExtension (L := F)).restrict Q).quotient (P.comap Q.subtype)).scalarExtension
        (L := L)).norm x z := by
  intro c A B
  let C := P.comap Q.subtype
  let D := A.comap B.subtype
  let e := finiteStageRestrictionEquiv (L := L) F Q
  let d := tensorQuotientBaseChangeEquiv (L := L) C
  have hMap : (C.baseChange L).map e.toLinearMap = D :=
    finiteStageRestrictionEquiv_map_subquotient_kernel (L := L) F P Q hPQ
  let q := Submodule.Quotient.equiv (C.baseChange L) D e hMap
  have hq := nativeStage_quotient_tower_norm_eq F
    (((ξ.scalarExtension (L := F)).restrict Q).scalarExtension (L := L))
    ((ξ.scalarExtension (L := L)).restrict B) e (C.baseChange L) D hMap x
    (fun t ↦ scalarExtension_restrict_tower_norm_eq ξ hi Q B e.toLinearMap rfl x t)
    (d.toLinearMap.baseChange x.abv.Completion z)
  have hd := nativeStage_tensorQuotient_norm_eq ((ξ.scalarExtension (L := F)).restrict Q)
    hi C x z
  have hv : (finiteStageSubquotientEquiv (L := L) F P Q hPQ).toLinearMap.baseChange
      x.abv.Completion z = q.toLinearMap.baseChange x.abv.Completion
        (d.toLinearMap.baseChange x.abv.Completion z) := by
    exact congrArg (fun f : _ →ₗ[x.abv.Completion] _ => f z)
      (LinearMap.baseChange_comp d.toLinearMap q.toLinearMap)
  exact (congrArg (fun t : x.abv.Completion ⊗[L] (B ⧸ D) =>
    (((ξ.scalarExtension (L := L)).restrict B).quotient D).norm
      (scalarExtensionTowerPlace x) t) hv).trans (hq.trans hd)

/-- An extended subquotient admits a linear equivalence preserving every completed norm and rank.

This transparent predicate packages the quotient spaces over an arbitrary algebraic tower,
so it also applies to subquotients descended to a finite intermediate field. -/
abbrev HasScalarExtensionSubquotientIsometry (ξ : NormFamily S E)
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L]
    (P₀ Q₀ : Submodule F (F ⊗[K] E)) (P Q : Submodule L (L ⊗[K] E)) : Prop :=
  ∃ e : (L ⊗[F] (Q₀ ⧸ P₀.comap Q₀.subtype)) ≃ₗ[L] (Q ⧸ P.comap Q.subtype),
    (∀ (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension F) L)
      (z : x.abv.Completion ⊗[L] (L ⊗[F] (Q₀ ⧸ P₀.comap Q₀.subtype))),
      (((ξ.scalarExtension (L := L)).restrict Q).quotient (P.comap Q.subtype)).norm
        (scalarExtensionTowerPlace x) (e.toLinearMap.baseChange x.abv.Completion z) =
        ((((ξ.scalarExtension (L := F)).restrict Q₀).quotient
          (P₀.comap Q₀.subtype)).scalarExtension (L := L)).norm x z) ∧
    Module.finrank L (Q ⧸ P.comap Q.subtype) =
      Module.finrank F (Q₀ ⧸ P₀.comap Q₀.subtype)

/-- Exact scalar-extension images admit a completed subquotient isometry preserving rank. -/
theorem hasScalarExtensionSubquotientIsometry_of_images (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (F : Type*) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]
    [Algebra.IsAlgebraic K F] [Algebra.IsAlgebraic F L] (hi : ∃ a : F, a ^ 2 = -1)
    (P₀ Q₀ : Submodule F (F ⊗[K] E)) (hPQ : P₀ ≤ Q₀)
    (P Q : Submodule L (L ⊗[K] E))
    (hP : (P₀.baseChange L).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = P)
    (hQ : (Q₀.baseChange L).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = Q) :
    ξ.HasScalarExtensionSubquotientIsometry F P₀ Q₀ P Q := by
  subst Q
  subst P
  refine ⟨finiteStageSubquotientEquiv (L := L) F P₀ Q₀ hPQ, ?_, ?_⟩
  · intro x z
    exact ξ.scalarExtension_subquotient_finiteStage_norm_eq F hi P₀ Q₀ hPQ x z
  · rw [← (finiteStageSubquotientEquiv (L := L) F P₀ Q₀ hPQ).finrank_eq,
      Module.finrank_baseChange]

/-- One produced complexifying finite field descends both actual nested target
subspaces and their genuine quotient, with exact endpoint images, actual rank,
and all-completed native norm preservation. -/
theorem exists_complexFiniteStage_subquotient_isometry [IsAlgClosed L]
    (ξ : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    (P Q : Submodule L (L ⊗[K] E)) (hPQ : P ≤ Q) :
    ∃ F : AdelicStructure.FiniteIntermediateField K L, (∃ a : F, a ^ 2 = -1) ∧
      ∃ P₀ Q₀ : Submodule F (F ⊗[K] E), P₀ ≤ Q₀ ∧
        (P₀.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = P ∧
        (Q₀.baseChange L).map
          (TensorProduct.AlgebraTensorModule.cancelBaseChange K F L L E).toLinearMap = Q ∧
        ξ.HasScalarExtensionSubquotientIsometry F P₀ Q₀ P Q := by
  let A : Fin 2 → Submodule L (L ⊗[K] E) := fun i => if i = 0 then P else Q
  let h := exists_complexFiniteStage_subspaces A
  let F := h.choose
  have hi := h.choose_spec.1
  let B := h.choose_spec.2.choose
  have hB := h.choose_spec.2.choose_spec.1
  have hInc := h.choose_spec.2.choose_spec.2.2
  have h01 : B 0 ≤ B 1 := (hInc 0 1).2 (by simpa [A] using hPQ)
  have h0 := hB 0
  have h1 := hB 1
  simp only [A, ite_eq_left rfl] at h0
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [A, h10, ite_false] at h1
  refine ⟨F, hi, B 0, B 1, h01, h0, h1, ?_⟩
  exact hasScalarExtensionSubquotientIsometry_of_images ξ F hi
    (B 0) (B 1) h01 P Q h0 h1

end NormFamily
end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurable automorphisms of extension parameter spaces

Chen–Moriwaki, Proposition 3.6.1, for every algebraic extension, without a
normality or finiteness hypothesis. We use the source's pullback convention
`|a|_{Tτ x} = |τ a|_x`, which reverses composition of automorphisms.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

open MeasureTheory

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L]

/-- Pullback of an extension place by a base-field automorphism, with the convention of
Chen–Moriwaki, §3.6: the value at `a` after pullback is the original value at `τ a`. -/
def aut (τ : L ≃ₐ[K] L) (x : ParameterSpaceExtension AS L) :
    ParameterSpaceExtension AS L where
  base := x.base
  abv := x.abv.pullback τ.toRingHom
  restrict_eq := by
    ext a
    change x.abv (τ (algebraMap K L a)) = AS.ϕ x.base a
    rw [τ.commutes]
    exact congrArg (fun v : AbsoluteValue K ℝ ↦ v a) x.restrict_eq

/-- An automorphism fixes the base parameter. -/
@[simp]
theorem aut_proj (τ : L ≃ₐ[K] L) (x : ParameterSpaceExtension AS L) :
    (aut AS L τ x).proj = x.proj := rfl

/-- Evaluation after automorphism pullback is evaluation at the transformed element. -/
@[simp]
theorem aut_eval (τ : L ≃ₐ[K] L) (x : ParameterSpaceExtension AS L) (a : L) :
    (aut AS L τ x).ϕ a = x.ϕ (τ a) := rfl

/-- The identity automorphism fixes every extension place. -/
@[simp]
theorem aut_refl (x : ParameterSpaceExtension AS L) :
    aut AS L (AlgEquiv.refl : L ≃ₐ[K] L) x = x := by
  apply ext AS L rfl
  ext a
  rfl

/-- Pullback reverses composition of automorphisms. -/
theorem aut_trans (τ σ : L ≃ₐ[K] L) (x : ParameterSpaceExtension AS L) :
    aut AS L (τ.trans σ) x = aut AS L τ (aut AS L σ x) := by
  apply ext AS L rfl
  ext a
  rfl

/-- Pulling back by an automorphism and its inverse returns the original place. -/
@[simp]
theorem aut_symm_aut (τ : L ≃ₐ[K] L) (x : ParameterSpaceExtension AS L) :
    aut AS L τ.symm (aut AS L τ x) = x := by
  refine ext AS L ?_ ?_
  · rfl
  · ext a
    change x.abv (τ (τ.symm a)) = x.abv a
    rw [τ.apply_symm_apply]

/-- Pulling back first by the inverse returns the original place as well. -/
@[simp]
theorem aut_aut_symm (τ : L ≃ₐ[K] L) (x : ParameterSpaceExtension AS L) :
    aut AS L τ (aut AS L τ.symm x) = x :=
  aut_symm_aut AS L τ.symm x

/-- Automorphism pullback is measurable for the evaluation-generated sigma algebra. -/
theorem measurable_aut (τ : L ≃ₐ[K] L) : Measurable (aut AS L τ) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap _ (_ ⊔ ⨆ a : L, _) ≤ _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  refine sup_le ?_ (iSup_le fun a ↦ ?_)
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_proj AS L).comap_le
  · rw [MeasurableSpace.comap_comp]
    exact (measurable_eval AS L (τ a)).comap_le

/-- An automorphism induces a measurable equivalence of the extension parameter space. -/
def autMeasurableEquiv (τ : L ≃ₐ[K] L) :
    ParameterSpaceExtension AS L ≃ᵐ ParameterSpaceExtension AS L where
  toFun := aut AS L τ
  invFun := aut AS L τ.symm
  left_inv := aut_symm_aut AS L τ
  right_inv := aut_aut_symm AS L τ
  measurable_toFun := measurable_aut AS L τ
  measurable_invFun := measurable_aut AS L τ.symm

/-- Proposition 3.6.1: the action is measurable for the sigma algebra of the algebraic
extension adelic structure. No finiteness, normality or separability is required. -/
theorem measurable_aut_projective [Algebra.IsAlgebraic K L] (τ : L ≃ₐ[K] L) :
    @Measurable (ParameterSpaceExtension AS L) (ParameterSpaceExtension AS L)
      (Algebraic.projectiveMeasurableSpace AS L) (Algebraic.projectiveMeasurableSpace AS L)
      (aut AS L τ) := by
  rw [Algebraic.projectiveMeasurableSpace_eq AS L]
  exact measurable_aut AS L τ

section Finite

variable [FiniteDimensional K L]

/-- The maximum over the finite automorphism orbit, the function `\tilde F` in the proof of
Chen–Moriwaki, Proposition 3.6.2. It is defined even when the extension is not normal. -/
noncomputable def orbitMaximum (F : ParameterSpaceExtension AS L → ℝ)
    (x : ParameterSpaceExtension AS L) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun τ : L ≃ₐ[K] L ↦ F (aut AS L τ x)

/-- Every value on an automorphism orbit is bounded by its maximum. -/
theorem apply_aut_le_orbitMaximum (F : ParameterSpaceExtension AS L → ℝ)
    (x : ParameterSpaceExtension AS L) (τ : L ≃ₐ[K] L) :
    F (aut AS L τ x) ≤ orbitMaximum AS L F x :=
  Finset.le_sup' (fun σ : L ≃ₐ[K] L ↦ F (aut AS L σ x)) (Finset.mem_univ τ)

/-- The orbit maximum is the least upper bound of the values on the orbit. -/
theorem orbitMaximum_le (F : ParameterSpaceExtension AS L → ℝ)
    (x : ParameterSpaceExtension AS L) {b : ℝ}
    (hb : ∀ τ : L ≃ₐ[K] L, F (aut AS L τ x) ≤ b) : orbitMaximum AS L F x ≤ b :=
  Finset.sup'_le _ _ (fun τ _ ↦ hb τ)

/-- An orbit maximum is attained by an automorphism. -/
theorem exists_aut_eq_orbitMaximum (F : ParameterSpaceExtension AS L → ℝ)
    (x : ParameterSpaceExtension AS L) :
    ∃ τ : L ≃ₐ[K] L, F (aut AS L τ x) = orbitMaximum AS L F x := by
  obtain ⟨τ, _, hτ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun τ : L ≃ₐ[K] L ↦ F (aut AS L τ x))
  exact ⟨τ, hτ.symm⟩

/-- The identity automorphism shows that a function is bounded by its orbit maximum. -/
theorem le_orbitMaximum (F : ParameterSpaceExtension AS L → ℝ)
    (x : ParameterSpaceExtension AS L) : F x ≤ orbitMaximum AS L F x := by
  simpa only [aut_refl] using apply_aut_le_orbitMaximum AS L F x AlgEquiv.refl

/-- Proposition 3.6.1 makes the finite maximum over automorphisms measurable. -/
theorem measurable_orbitMaximum {F : ParameterSpaceExtension AS L → ℝ}
    (hF : Measurable F) : Measurable (orbitMaximum AS L F) := by
  have he : orbitMaximum AS L F = Finset.univ.sup' Finset.univ_nonempty
      (fun τ : L ≃ₐ[K] L ↦ fun x ↦ F (aut AS L τ x)) := by
    funext x
    exact (Finset.sup'_apply Finset.univ_nonempty
      (fun τ : L ≃ₐ[K] L ↦ fun x ↦ F (aut AS L τ x)) x).symm
  rw [he]
  exact Finset.measurable_sup' Finset.univ_nonempty
    (fun τ _ ↦ hF.comp (measurable_aut AS L τ))

/-- Taking the orbit maximum makes a function invariant under every automorphism. -/
@[simp]
theorem orbitMaximum_aut (F : ParameterSpaceExtension AS L → ℝ)
    (σ : L ≃ₐ[K] L) (x : ParameterSpaceExtension AS L) :
    orbitMaximum AS L F (aut AS L σ x) = orbitMaximum AS L F x := by
  apply le_antisymm
  · apply orbitMaximum_le
    intro τ
    rw [← aut_trans]
    exact apply_aut_le_orbitMaximum AS L F x (τ.trans σ)
  · apply orbitMaximum_le
    intro τ
    have h := apply_aut_le_orbitMaximum AS L F (aut AS L σ x) (τ.trans σ.symm)
    simpa only [aut_trans, aut_symm_aut] using h

/-- The orbit maximum is the least invariant majorant. -/
theorem orbitMaximum_le_of_invariant {F G : ParameterSpaceExtension AS L → ℝ}
    (hFG : ∀ x, F x ≤ G x)
    (hG : ∀ (τ : L ≃ₐ[K] L) x, G (aut AS L τ x) = G x)
    (x : ParameterSpaceExtension AS L) : orbitMaximum AS L F x ≤ G x := by
  apply orbitMaximum_le
  intro τ
  exact (hFG (aut AS L τ x)).trans_eq (hG τ x)

end Finite

end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

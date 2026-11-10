/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.PicardGroup

/-!
# Bounded-index elements in actual number-field ideals

Finite ideal classes supply a field-dependent bound for an actual cyclic
quotient of every nonzero integral or fractional ideal. The existing
classification of invertible modules as ideals then proves source Lemma
4.4.11 for arbitrary actual invertible modules over the ring of integers.
-/

@[expose] public section

open scoped NumberField nonZeroDivisors

noncomputable section

namespace ArakelovGeometry.NumberFieldBoundedIndex

variable (K : Type*) [Field K] [NumberField K]

/-- A nonzero actual integral representative of each ideal class. -/
def classRepresentative (c : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  Classical.choose (ClassGroup.mk0_surjective c)

theorem classRepresentative_class (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk0 (classRepresentative K c) = c :=
  Classical.choose_spec (ClassGroup.mk0_surjective c)

/-- A single positive integer depending only on the number field. -/
def indexBound : ℕ :=
  1 + ∑ c : ClassGroup (𝓞 K), Ideal.absNorm (classRepresentative K c : Ideal (𝓞 K))

theorem indexBound_pos : 0 < indexBound K := by
  unfold indexBound
  omega

theorem classRepresentative_norm_le (c : ClassGroup (𝓞 K)) :
    Ideal.absNorm (classRepresentative K c : Ideal (𝓞 K)) ≤ indexBound K := by
  have h := Finset.single_le_sum (fun j _ => Nat.zero_le
    (Ideal.absNorm (classRepresentative K j : Ideal (𝓞 K)))) (Finset.mem_univ c)
  exact h.trans (Nat.le_add_left _ _)

/-- Principalization by an integral representative of the inverse class,
with a uniform norm bound. The element and its membership are produced. -/
theorem exists_bounded_principal_multiple (I : (Ideal (𝓞 K))⁰) :
    ∃ (J : (Ideal (𝓞 K))⁰) (x : 𝓞 K), x ≠ 0 ∧ x ∈ (I : Ideal (𝓞 K)) ∧
      (I : Ideal (𝓞 K)) * J = Ideal.span {x} ∧ Ideal.absNorm (J : Ideal (𝓞 K)) ≤
        indexBound K := by
  let J := classRepresentative K (ClassGroup.mk0 I)⁻¹
  have hclass : ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ := by
    rw [classRepresentative_class, inv_inv]
  obtain ⟨x, hx, hprod⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp hclass
  refine ⟨J, x, hx, ?_, hprod, classRepresentative_norm_le K _⟩
  have hle : Ideal.span {x} ≤ (I : Ideal (𝓞 K)) :=
    hprod ▸ Ideal.mul_le_left
  exact hle (Ideal.mem_span_singleton_self x)

/-- The actual product subideal has relative additive index equal to the
absolute norm of its second factor. -/
theorem ideal_product_relIndex (I J : (Ideal (𝓞 K))⁰) :
    ((I : Ideal (𝓞 K)) * J).toAddSubgroup.relIndex
      (I : Ideal (𝓞 K)).toAddSubgroup = Ideal.absNorm (J : Ideal (𝓞 K)) := by
  apply (mul_left_inj' (Ideal.absNorm_ne_zero_of_nonZeroDivisors I)).mp
  have h := AddSubgroup.relIndex_mul_index
    (show ((I : Ideal (𝓞 K)) * J).toAddSubgroup ≤
        (I : Ideal (𝓞 K)).toAddSubgroup from Ideal.mul_le_left)
  change _ * Ideal.absNorm (I : Ideal (𝓞 K)) = _ at h
  rw [← Ideal.absNorm_eq_index, map_mul] at h
  exact h.trans (mul_comm _ _)

omit [NumberField K] in
/-- The quotient by the actual cyclic submodule agrees with the relative
additive index of the corresponding principal ideal in its ambient ideal. -/
theorem ideal_cyclicQuotient_card_eq_relIndex (I : Ideal (𝓞 K)) (x : I) :
    Nat.card (I ⧸ Submodule.span (𝓞 K) {x}) =
      (Ideal.span {(x : 𝓞 K)}).toAddSubgroup.relIndex I.toAddSubgroup := by
  rw [← LinearMap.submoduleOf_span_singleton_of_mem I x.property]
  rfl

/-- Principalization gives the cardinality of the literal cyclic quotient,
not a norm ratio supplied as a certificate. -/
theorem ideal_cyclicQuotient_card_of_product (I J : (Ideal (𝓞 K))⁰)
    (x : (I : Ideal (𝓞 K)))
    (hprod : (I : Ideal (𝓞 K)) * J = Ideal.span {(x : 𝓞 K)}) :
    Nat.card ((I : Ideal (𝓞 K)) ⧸ Submodule.span (𝓞 K) {x}) =
      Ideal.absNorm (J : Ideal (𝓞 K)) := by
  rw [ideal_cyclicQuotient_card_eq_relIndex, ← hprod]
  exact ideal_product_relIndex K I J

/-- Every actual nonzero integral ideal contains a nonzero element with
finite cyclic quotient uniformly bounded in terms of the field alone. -/
theorem exists_integralIdeal_boundedIndex_element (I : (Ideal (𝓞 K))⁰) :
    ∃ x : (I : Ideal (𝓞 K)), x ≠ 0 ∧
      Finite ((I : Ideal (𝓞 K)) ⧸ Submodule.span (𝓞 K) {x}) ∧
      Nat.card ((I : Ideal (𝓞 K)) ⧸ Submodule.span (𝓞 K) {x}) ≤ indexBound K := by
  obtain ⟨J, x, hx, hxI, hprod, hbound⟩ := exists_bounded_principal_multiple K I
  let y : (I : Ideal (𝓞 K)) := ⟨x, hxI⟩
  have hy : y ≠ 0 := by
    intro h
    exact hx (congrArg Subtype.val h)
  have hcard := ideal_cyclicQuotient_card_of_product K I J y hprod
  refine ⟨y, hy, Nat.finite_of_card_ne_zero ?_, hcard ▸ hbound⟩
  rw [hcard]
  exact Ideal.absNorm_ne_zero_of_nonZeroDivisors J

/-- A linear equivalence descends to the actual quotients by a vector and
its image. -/
def cyclicQuotientEquiv {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (x : M) :
    (M ⧸ Submodule.span R {x}) ≃ₗ[R] (N ⧸ Submodule.span R {e x}) :=
  Submodule.Quotient.equiv _ _ e (by rw [Submodule.map_span, Set.image_singleton]; rfl)

theorem cyclicQuotient_card_eq {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (x : M) :
    Nat.card (M ⧸ Submodule.span R {x}) =
      Nat.card (N ⧸ Submodule.span R {e x}) :=
  Nat.card_congr (cyclicQuotientEquiv e x).toEquiv

/-- Denominator clearing transports the uniform bound to every actual
nonzero fractional ideal of the number field. -/
theorem exists_fractionalIdeal_boundedIndex_element
    (L : FractionalIdeal (𝓞 K)⁰ K) (hL : L ≠ 0) :
    ∃ x : (L : Submodule (𝓞 K) K), x ≠ 0 ∧
      Finite ((L : Submodule (𝓞 K) K) ⧸ Submodule.span (𝓞 K) {x}) ∧
      Nat.card ((L : Submodule (𝓞 K) K) ⧸ Submodule.span (𝓞 K) {x}) ≤ indexBound K := by
  let I : (Ideal (𝓞 K))⁰ :=
    ⟨L.num, mem_nonZeroDivisors_of_ne_zero (fun h =>
      hL ((FractionalIdeal.num_eq_zero_iff (I := L)).mp h))⟩
  let e : (L : Submodule (𝓞 K) K) ≃ₗ[𝓞 K] (I : Ideal (𝓞 K)) :=
    L.equivNumOfIsLocalization
  obtain ⟨y, hy, hfinite, hcard⟩ := exists_integralIdeal_boundedIndex_element K I
  let x := e.symm y
  have hx : x ≠ 0 := by
    intro h
    apply hy
    simpa only [x, e.apply_symm_apply, map_zero] using congrArg e h
  have heq : Nat.card ((L : Submodule (𝓞 K) K) ⧸ Submodule.span (𝓞 K) {x}) =
      Nat.card ((I : Ideal (𝓞 K)) ⧸ Submodule.span (𝓞 K) {y}) := by
    simpa only [x, e.apply_symm_apply] using cyclicQuotient_card_eq e x
  refine ⟨x, hx, Nat.finite_of_card_ne_zero ?_, heq ▸ hcard⟩
  rw [heq]
  let := hfinite
  exact Nat.card_pos.ne'

/-- Source Lemma 4.4.11 for an arbitrary actual invertible module, with
the same field-only bound as for ideals. No ideal model is assumed. -/
theorem exists_invertibleModule_boundedIndex_element
    (L : Type*) [AddCommGroup L] [Module (𝓞 K) L] [Module.Invertible (𝓞 K) L] :
    ∃ x : L, x ≠ 0 ∧ Finite (L ⧸ Submodule.span (𝓞 K) {x}) ∧
      Nat.card (L ⧸ Submodule.span (𝓞 K) {x}) ≤ indexBound K := by
  obtain ⟨I, ⟨e⟩⟩ := Module.Invertible.exists_linearEquiv_ideal (𝓞 K) L
  have hI : I ≠ 0 := by
    intro h
    have hL : ∀ x : L, x = 0 := by
      intro x
      apply e.injective
      apply Subtype.ext
      have hx := (e x).property
      simpa only [h, Ideal.zero_eq_bot, Ideal.mem_bot, map_zero, Submodule.coe_zero] using hx
    have h01 : (0 : 𝓞 K) = 1 :=
      eq_of_smul_eq_smul (α := L) (fun x => by rw [hL x]; simp)
    exact zero_ne_one h01
  let J : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩
  obtain ⟨y, hy, hfinite, hcard⟩ := exists_integralIdeal_boundedIndex_element K J
  let x := e.symm y
  have hx : x ≠ 0 := by
    intro h
    apply hy
    simpa only [x, e.apply_symm_apply, map_zero] using congrArg e h
  have heq : Nat.card (L ⧸ Submodule.span (𝓞 K) {x}) =
      Nat.card (I ⧸ Submodule.span (𝓞 K) {y}) := by
    simpa only [x, e.apply_symm_apply] using cyclicQuotient_card_eq e x
  refine ⟨x, hx, Nat.finite_of_card_ne_zero ?_, heq ▸ hcard⟩
  rw [heq]
  let := hfinite
  exact Nat.card_pos.ne'

end ArakelovGeometry.NumberFieldBoundedIndex

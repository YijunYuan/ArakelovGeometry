/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Finite descent through an algebraic base extension

Finite extensions descend, together with prescribed finite subsets, while preserving both
ordinary and separable degrees. The proof descends a multiplication table and a primitive
element of the separable closure. This supplies the finite-stage base-change argument for
Chen–Moriwaki, *Adelic curves*, Theorem 3.4.12.
-/

open Module
open scoped BigOperators
namespace IntermediateField
variable {A B N ι : Type*} [Field A] [Field B] [Field N]
  [Algebra A B] [Algebra B N] [Algebra A N] [IsScalarTower A B N]
  [Finite ι]
omit [Algebra A B] [Algebra B N] [IsScalarTower A B N] in
/-- A finite span containing one and the products of its generators is an intermediate field. -/
theorem exists_toSubmodule_eq_span_of_mul_mem (b : ι → N)
  (h1 : 1 ∈ Submodule.span A (Set.range b))
  (hmul : ∀ i j, b i * b j ∈ Submodule.span A (Set.range b)) :
  ∃ E : IntermediateField A N,
    E.toSubalgebra.toSubmodule = Submodule.span A (Set.range b) := by
  let V := Submodule.span A (Set.range b)
  have hmul' {x y : N} (hx : x ∈ V) (hy : y ∈ V) : x * y ∈ V := by
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      exact hmul i j
    | zero_left y hy => simp
    | zero_right x hx => simp
    | add_left x y z hx hy hz hxz hyz => simpa only [add_mul] using V.add_mem hxz hyz
    | add_right x y z hx hy hz hxy hxz => simpa only [mul_add] using V.add_mem hxy hxz
    | smul_left a x y hx hy hxy => simpa only [smul_mul_assoc] using V.smul_mem a hxy
    | smul_right a x y hx hy hxy => simpa only [mul_smul_comm] using V.smul_mem a hxy
  let S : Subalgebra A N := {
    carrier := V
    zero_mem' := V.zero_mem
    one_mem' := h1
    add_mem' := V.add_mem
    mul_mem' := hmul'
    algebraMap_mem' a := by
      change algebraMap A N a ∈ V
      simpa only [Algebra.smul_def, mul_one] using V.smul_mem a h1 }
  let : Module.Finite A S := Module.Finite.span_of_finite A (Set.finite_range b)
  exact ⟨S.toIntermediateField' (IsField.of_isDomain_of_finite A S), rfl⟩

variable {K : Type*} [Field K] [Algebra K B] [Algebra K N]
  [IsScalarTower K B N] [Algebra.IsAlgebraic K B]
omit [Algebra K N] [IsScalarTower K B N] in
/-- Descend a finite basis and prescribed finite sets to a finite extension of the ground field. -/
theorem exists_finite_basis_descent (b : Basis ι B N) (s : Set N) (hs : s.Finite)
  (t : Set B) (ht : t.Finite) :
  ∃ (A : IntermediateField K B), Module.Finite K A ∧ t ⊆ A ∧
    ∃ E : IntermediateField A N,
      E.toSubalgebra.toSubmodule = Submodule.span A (Set.range b) ∧ s ⊆ E := by
  classical
  let : Finite s := hs.to_subtype
  let C : Set B := t ∪ (Set.range (fun i ↦ b.repr 1 i) ∪
    (Set.range (fun ijk : ι × ι × ι ↦ b.repr (b ijk.1 * b ijk.2.1) ijk.2.2) ∪
      Set.range (fun xi : s × ι ↦ b.repr xi.1.val xi.2)))
  have hC : C.Finite := ht.union ((Set.finite_range _).union
    ((Set.finite_range _).union (Set.finite_range _)))
  let A := IntermediateField.adjoin K C
  let : Finite C := hC.to_subtype
  have hA : Module.Finite K A := IntermediateField.finiteDimensional_adjoin
    fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have hc {x : B} (hx : x ∈ C) : x ∈ A := IntermediateField.subset_adjoin K C hx
  have hm (x : N) (hx : ∀ i, b.repr x i ∈ A) :
      x ∈ Submodule.span A (Set.range b) :=
    (b.mem_span_iff_repr_mem A x).mpr fun i ↦ ⟨⟨_, hx i⟩, rfl⟩
  have h1 : 1 ∈ Submodule.span A (Set.range b) :=
    hm 1 fun i ↦ hc (Or.inr (Or.inl ⟨i, rfl⟩))
  have hmul (i j : ι) : b i * b j ∈ Submodule.span A (Set.range b) :=
    hm _ fun k ↦ hc (Or.inr (Or.inr (Or.inl ⟨⟨i, j, k⟩, rfl⟩)))
  obtain ⟨E, hE⟩ := exists_toSubmodule_eq_span_of_mul_mem b h1 hmul
  refine ⟨A, hA, fun x hx ↦ hc (Or.inl hx), E, hE, ?_⟩
  intro x hx
  change x ∈ E.toSubalgebra.toSubmodule
  rw [hE]
  exact hm x fun i ↦ hc (Or.inr (Or.inr (Or.inr ⟨⟨⟨x, hx⟩, i⟩, rfl⟩)))

omit [Algebra A B] [Algebra A N] [IsScalarTower A B N]
  [Algebra K N] [IsScalarTower K B N] [Algebra.IsAlgebraic K B] in
/-- A field spanned over the smaller base by a basis over the larger base has the same degree
and generates the ambient field after adjoining the larger base. -/
theorem finiteDimensional_finrank_adjoin_of_basis_span (b : Basis ι B N) (A : IntermediateField K B)
  (E : IntermediateField A N)
  (hE : E.toSubalgebra.toSubmodule = Submodule.span A (Set.range b)) :
  Module.Finite A E ∧ Module.finrank A E = Module.finrank B N ∧
    IntermediateField.adjoin B (E : Set N) = ⊤ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hfin : Module.Finite A E := by
    change Module.Finite A E.toSubalgebra.toSubmodule
    rw [hE]
    exact Module.Finite.span_of_finite A (Set.finite_range b)
  refine ⟨hfin, ?_, ?_⟩
  · change Module.finrank A E.toSubalgebra.toSubmodule = _
    rw [hE, Module.finrank_eq_card_basis (Basis.span (b.linearIndependent.restrict_scalars' A)),
      Module.finrank_eq_card_basis b]
  · have hi (i : ι) : b i ∈ E := by
      change b i ∈ E.toSubalgebra.toSubmodule
      rw [hE]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hle : Submodule.span B (Set.range b) ≤
        (IntermediateField.adjoin B (E : Set N)).toSubalgebra.toSubmodule :=
      Submodule.span_le.mpr fun x ⟨i, hi'⟩ ↦ hi' ▸ IntermediateField.subset_adjoin B _ (hi i)
    rw [b.span_eq] at hle
    apply top_unique
    intro x _
    exact hle (Submodule.mem_top)
end IntermediateField

open Polynomial in
/-- A primitive element of the separable closure generates a power of every ambient element. -/
theorem Field.exists_separable_generator_pow_aeval {B N : Type*} [Field B] [Field N] [Algebra B N]
  [FiniteDimensional B N] (q : ℕ) [ExpChar B q] :
  ∃ c : N, IsSeparable B c ∧ (minpoly B c).natDegree = Field.finSepDegree B N ∧
    ∀ x : N, ∃ n : ℕ, ∃ P : B[X], aeval c P = x ^ q ^ n := by
  classical
  let C := separableClosure B N
  let pb := Field.powerBasisOfFiniteOfSeparable B C
  refine ⟨pb.gen.val, pb.gen.property, ?_, ?_⟩
  · change (minpoly B (C.val pb.gen)).natDegree = _
    rw [minpoly.algHom_eq C.val C.val.injective pb.gen,
      pb.natDegree_minpoly, ← pb.finrank]
    have h := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic B C N
    rw [IsPurelyInseparable.finSepDegree_eq_one (F := C) (E := N), mul_one,
      Field.finSepDegree_eq_finrank_of_isSeparable] at h
    exact h
  · intro x
    obtain ⟨n, z, hz⟩ := IsPurelyInseparable.pow_mem C q x
    obtain ⟨P, hP⟩ := pb.exists_eq_aeval' z
    refine ⟨n, P, ?_⟩
    rw [show (pb.gen.val : N) = C.val pb.gen from rfl, Polynomial.aeval_algHom_apply, ← hP]
    exact hz

open Module Polynomial in
/-- A finite extension of an algebraic extension descends to a finite ground-field extension,
containing any prescribed finite subset and preserving total and separable degrees. -/
theorem IntermediateField.exists_finite_descent_of_finite_subset
    {K B N : Type*} [Field K] [Field B] [Field N]
  [Algebra K B] [Algebra B N] [Algebra.IsAlgebraic K B] [FiniteDimensional B N]
  (s : Set N) (hs : s.Finite) :
  ∃ (A : IntermediateField K B), Module.Finite K A ∧
    ∃ E : IntermediateField A N, Module.Finite A E ∧ s ⊆ E ∧
     IntermediateField.adjoin B (E : Set N) = ⊤ ∧
     Module.finrank A E = Module.finrank B N ∧
     Field.finSepDegree A E = Field.finSepDegree B N := by
  classical
  let b := Module.finBasis B N
  let q := ringExpChar B
  obtain ⟨c, hc, hdeg, hpow⟩ := Field.exists_separable_generator_pow_aeval (B := B) (N := N) q
  choose n P hP using fun i ↦ hpow (b i)
  let t : Set B := Set.range (minpoly B c).coeff ∪ ⋃ i, Set.range (P i).coeff
  have ht : t.Finite := (minpoly B c).finite_range_coeff.union
    (Set.finite_iUnion fun i ↦ (P i).finite_range_coeff)
  obtain ⟨A, hA, htA, E, hE, hsE⟩ := IntermediateField.exists_finite_basis_descent
    (K := K) b (insert c s) (hs.insert c) t ht
  obtain ⟨hfin, hfinrank, hgen⟩ :=
    IntermediateField.finiteDimensional_finrank_adjoin_of_basis_span b A E hE
  let : Module.Finite A E := hfin
  let cE : E := ⟨c, hsE (Set.mem_insert _ _)⟩
  have hclift : minpoly B c ∈ lifts (algebraMap A B) := by
    apply (lifts_iff_coeff_lifts _).mpr
    intro k
    exact ⟨⟨_, htA (Or.inl ⟨k, rfl⟩)⟩, rfl⟩
  have hci : IsIntegral A c := IsIntegral.map E.val (Algebra.IsIntegral.isIntegral cE)
  have hmin := minpoly.map_algebraMap hci hclift
  have hcE : IsSeparable A cE := by
    change (minpoly A cE).Separable
    rw [IntermediateField.minpoly_eq]
    exact (separable_map (algebraMap A B)).mp (hmin ▸ hc)
  let D := IntermediateField.adjoin A {cE}
  have : Algebra.IsSeparable A D :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable A E).mpr hcE
  have hbE (i) : b i ∈ E := by
    change b i ∈ E.toSubalgebra.toSubmodule
    rw [hE]
    exact Submodule.subset_span ⟨i, rfl⟩
  let bE := fun i ↦ (⟨b i, hbE i⟩ : E)
  have hspan : Submodule.span A (Set.range bE) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := E.val.toLinearMap) E.val.injective
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top]
    have hr : E.val.toLinearMap.range = E.toSubalgebra.toSubmodule := by
      ext x
      exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
    rw [hr]
    exact hE.symm
  have hpi (i) : P i ∈ lifts (algebraMap A B) := by
    apply (lifts_iff_coeff_lifts _).mpr
    intro k
    exact ⟨⟨_, htA (Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨k, rfl⟩⟩))⟩, rfl⟩
  have hpure : IsPurelyInseparable D E := by
    apply isPurelyInseparable_iff_perfectClosure_eq_top.mpr
    have hle : Submodule.span A (Set.range bE) ≤
        ((perfectClosure D E).restrictScalars A).toSubalgebra.toSubmodule := by
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts _).mp (hpi i)
      have hpowE : (bE i) ^ q ^ n i = aeval cE Q := by
        apply E.val.injective
        change (b i) ^ q ^ n i = E.val (aeval cE Q)
        rw [← Polynomial.aeval_algHom_apply]
        change (b i) ^ q ^ n i = aeval c Q
        rw [← aeval_map_algebraMap B, hQ]
        exact (hP i).symm
      apply mem_perfectClosure_iff.mpr
      have : ExpChar N q := ((algebraMap B N).expChar_iff
        (algebraMap B N).injective q).mp inferInstance
      refine ⟨n i, ?_⟩
      rw [ringExpChar.eq D q, hpowE]
      refine ⟨aeval (⟨cE, IntermediateField.mem_adjoin_simple_self A cE⟩ : D) Q, ?_⟩
      exact (Polynomial.aeval_algHom_apply D.val _ Q).symm
    rw [hspan] at hle
    apply top_unique
    intro x _
    exact hle Submodule.mem_top
  let : IsPurelyInseparable D E := hpure
  refine ⟨A, hA, E, hfin, fun x hx ↦ hsE (Set.mem_insert_of_mem _ hx), hgen, hfinrank, ?_⟩
  have htower := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic A D E
  rw [IsPurelyInseparable.finSepDegree_eq_one (F := D) (E := E), mul_one,
    Field.finSepDegree_eq_finrank_of_isSeparable] at htower
  rw [← htower, IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral cE),
    IntermediateField.minpoly_eq]
  exact (Polynomial.natDegree_map (algebraMap A B)).symm.trans
    ((congrArg Polynomial.natDegree hmin).trans hdeg)

open Module in
/-- Finite descent may contain a prescribed finite intermediate extension of the ground field. -/
theorem IntermediateField.exists_finite_descent {K B N : Type*} [Field K] [Field B] [Field N]
  [Algebra K B] [Algebra B N] [Algebra K N] [IsScalarTower K B N]
  [Algebra.IsAlgebraic K B] [FiniteDimensional B N]
  (F : IntermediateField K N) [FiniteDimensional K F] :
  ∃ (A : IntermediateField K B), Module.Finite K A ∧
    ∃ E : IntermediateField A N, Module.Finite A E ∧ F ≤ E.restrictScalars K ∧
     IntermediateField.adjoin B (E : Set N) = ⊤ ∧
     Module.finrank A E = Module.finrank B N ∧
     Field.finSepDegree A E = Field.finSepDegree B N := by
  classical
  let b := Module.finBasis K F
  obtain ⟨A, hA, E, hE, hs, hgen, hfin, hsep⟩ :=
    IntermediateField.exists_finite_descent_of_finite_subset (K := K) (B := B)
    (Set.range fun i ↦ (b i : N)) (Set.finite_range _)
  refine ⟨A, hA, E, hE, ?_, hgen, hfin, hsep⟩
  intro x hx
  let V := (E.restrictScalars K).toSubalgebra.toSubmodule
  change x ∈ V
  have heq := congrArg F.val (b.sum_repr ⟨x, hx⟩)
  simp only [map_sum, map_smul] at heq
  change (∑ i, b.repr ⟨x, hx⟩ i • (b i : N)) = x at heq
  rw [← heq]
  exact V.sum_mem fun i _ ↦ V.smul_mem _ (hs ⟨i, rfl⟩)

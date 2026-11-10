/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.ParameterSpace
public import ArakelovGeometry.AdelicCurve.Extension.PowerSums
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Minpoly.IsConjRoot
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.RingTheory.Trace.Basic

/-!
# Measurable averages over embeddings

Orbit maxima and ordered absolute values prove measurability of embedding averages
for finite separable extensions (Chen–Moriwaki, Lemma 3.3.5).
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u v w

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (L : Type w) [Field L] [Algebra K L]

variable (K) in
/-- The power sums of the embeddings of a finite separable extension are traces. -/
theorem sum_pow_embeddings_eq_trace {E : Type*} [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (b : E) (N : ℕ) :
    (∑ σ : E →ₐ[K] AlgebraicClosure K, (σ b) ^ N) =
      algebraMap K (AlgebraicClosure K) (Algebra.trace K E (b ^ N)) := by
  simpa only [map_pow] using (trace_eq_sum_embeddings (AlgebraicClosure K)
    (x := b ^ N)).symm

variable (K) in
/-- Every embedding of a simple subextension of an algebraic closure extends to an
automorphism of the algebraic closure. -/
theorem adjoin_restrict_aut_surjective (c : AlgebraicClosure K) :
    Function.Surjective (fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦
      τ.toAlgHom.comp (IntermediateField.adjoin K {c}).val) := by
  intro σ
  let f := σ.liftNormal (AlgebraicClosure K)
  let e := AlgEquiv.ofBijective f (AlgHom.normal_bijective K (AlgebraicClosure K)
    (AlgebraicClosure K) f)
  refine ⟨e, ?_⟩
  ext x
  exact σ.liftNormal_commutes (AlgebraicClosure K) x

variable (K) in
/-- Embeddings of a simple extension are determined by the image of its generator. -/
theorem adjoin_embeddings_gen_injective (c : AlgebraicClosure K) :
    Function.Injective (fun σ : (IntermediateField.adjoin K {c}) →ₐ[K] AlgebraicClosure K ↦
      σ (IntermediateField.AdjoinSimple.gen K c)) := by
  intro σ τ h
  apply (IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral c)).algHom_ext
  simpa only [IntermediateField.adjoin.powerBasis_gen] using h

/-- The orbit of an algebraic element is exactly the root set of its minimal polynomial. -/
theorem range_aut_eq_minpoly_rootSet (c : AlgebraicClosure K) :
    Set.range (fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦ τ c) =
      (minpoly K c).rootSet (AlgebraicClosure K) := by
  ext a
  rw [← isConjRoot_iff_mem_minpoly_rootSet (Algebra.IsIntegral.isIntegral c),
    IsConjRoot.comm, isConjRoot_iff_exists_algEquiv]
  rfl
/-- A separable simple extension has one conjugate for each dimension over its base. -/
theorem natCard_separable_orbit (c : AlgebraicClosure K) (hc : IsSeparable K c) :
    Nat.card (Set.range (fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦ τ c)) =
      Module.finrank K (IntermediateField.adjoin K {c}) := by
  classical
  let E := IntermediateField.adjoin K {c}
  let : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hc.isIntegral
  let : Algebra.IsSeparable K E :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K (AlgebraicClosure K)).mpr hc
  have hrange : Set.range (fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦ τ c) =
      Set.range (fun σ : E →ₐ[K] AlgebraicClosure K ↦
        σ (IntermediateField.AdjoinSimple.gen K c)) := by
    ext a
    constructor
    · rintro ⟨τ, rfl⟩
      exact ⟨τ.toAlgHom.comp E.val, rfl⟩
    · rintro ⟨σ, rfl⟩
      obtain ⟨τ, hτ⟩ := adjoin_restrict_aut_surjective K c σ
      exact ⟨τ, congrArg (fun f : E →ₐ[K] AlgebraicClosure K ↦
        f (IntermediateField.AdjoinSimple.gen K c)) hτ⟩
  rw [hrange, ← Nat.card_congr (Equiv.ofInjective _
    (adjoin_embeddings_gen_injective K c)), Nat.card_eq_fintype_card]
  exact AlgHom.card K E (AlgebraicClosure K)

/-- Chen--Moriwaki, Lemma 3.3.5(2): given any choice of extensions of the base absolute
values to an algebraic closure of `K`, the maximal absolute value on the Galois orbit of a
separable element is a measurable function of the base point. -/
theorem measurable_iSup_abv_aut (s : AS.Ω → ParameterSpaceExtension AS (AlgebraicClosure K))
    (hs : ∀ ω, (s ω).proj = ω) {c : AlgebraicClosure K} (hc : IsSeparable K c) :
    Measurable fun ω : AS.Ω ↦
      ⨆ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (s ω).ϕ (τ c) := by
 classical
  let E := IntermediateField.adjoin K {c}
  let : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hc.isIntegral
  let : Algebra.IsSeparable K E :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K (AlgebraicClosure K)).mpr hc
  let e : Fin (Module.finrank K E) ≃ (E →ₐ[K] AlgebraicClosure K) :=
    (Fintype.equivFinOfCardEq (AlgHom.card K E (AlgebraicClosure K))).symm
  let b : E := IntermediateField.AdjoinSimple.gen K c
  let α (i : Fin (Module.finrank K E)) := e i b
  have hα : Function.Injective α := (adjoin_embeddings_gen_injective K c).comp e.injective
  have hd : 1 ≤ Module.finrank K E := Module.finrank_pos
  have hsum (N : ℕ) : (∑ i, α i ^ N) =
      algebraMap K (AlgebraicClosure K) (Algebra.trace K E (b ^ N)) := by
    calc
      _ = ∑ σ : E →ₐ[K] AlgebraicClosure K, σ b ^ N :=
        Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
      _ = _ := sum_pow_embeddings_eq_trace K b N
  have hrest (ω : AS.Ω) (a : K) :
      (s ω).ϕ (algebraMap K (AlgebraicClosure K) a) = AS.ϕ ω a := by
    have h := (ParameterSpaceExtension.ϕ_restriction AS (AlgebraicClosure K) (s ω)).trans
      (congrArg AS.ϕ (hs ω))
    exact congrArg (fun v : AbsoluteValue K ℝ ↦ v a) h
  have heq (ω : AS.Ω) :
      (⨆ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (s ω).ϕ (τ c)) =
        Filter.limsup (fun N : ℕ ↦
          (AS.ϕ ω (Algebra.trace K E (b ^ N))) ^ ((N : ℝ)⁻¹)) Filter.atTop := by
    calc
      _ = ⨆ σ : E →ₐ[K] AlgebraicClosure K, (s ω).ϕ (σ b) :=
        (adjoin_restrict_aut_surjective K c).iSup_comp _
      _ = ⨆ i, (s ω).ϕ (α i) := e.iSup_comp.symm
      _ = _ := by
        rw [(s ω).ϕ.iSup_eq_limsup_sum_pow_rpow hd hα]
        simp_rw [hsum, hrest]
  simp_rw [heq]
  apply Measurable.limsup
  intro N
  apply Measurable.pow_const
  let a := Algebra.trace K E (b ^ N)
  change Measurable fun ω ↦ AS.ϕ ω a
  by_cases ha : a = 0
  · simp only [ha, map_zero]
    exact measurable_const
  · have heval : (fun ω ↦ AS.ϕ ω a) = fun ω ↦ Real.exp (Real.log (AS.ϕ ω a)) := by
      funext ω
      exact (Real.exp_log ((AS.ϕ ω).pos ha)).symm
    rw [heval]
    exact (AS.measurable_log a ha).exp


variable (K) in
/-- The maximal products of fixed numbers of embedding values are measurable by the
Galois orbit maximum formula. -/
theorem measurable_iSup_prod_embeddings {E : Type*} [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (s : AS.Ω → ParameterSpaceExtension AS (AlgebraicClosure K))
    (hs : ∀ ω, (s ω).proj = ω) (b : E) (k : ℕ)
    (hk : k ≤ Fintype.card (E →ₐ[K] AlgebraicClosure K)) :
    Measurable fun ω ↦
      ⨆ J : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k},
        ∏ σ ∈ J.val, (s ω).ϕ (σ b) := by
  classical
  let e := Fintype.equivFin (E →ₐ[K] AlgebraicClosure K)
  let J₀ : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k} :=
    ⟨(Finset.univ.map (Fin.castLEEmb hk)).map e.symm.toEmbedding, by simp⟩
  let : Nonempty {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k} := ⟨J₀⟩
  let P (ω : AS.Ω) := ⨆ J : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k},
    ∏ σ ∈ J.val, (s ω).ϕ (σ b)
  have hbound (ω : AS.Ω)
      (J : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k})
      (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
      (s ω).ϕ (τ (∏ σ ∈ J.val, σ b)) ≤ P ω := by
    let p := (AlgEquiv.refl : E ≃ₐ[K] E).arrowCongr τ
    let J' : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k} :=
      ⟨J.val.map p.toEmbedding, by simpa using J.property⟩
    apply Finite.le_ciSup_of_le J'
    simp only [J', Finset.prod_map]
    rw [_root_.map_prod, AbsoluteValue.map_prod]
    rfl
  have heq (ω : AS.Ω) : P ω =
      ⨆ J : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k},
        ⨆ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          (s ω).ϕ (τ (∏ σ ∈ J.val, σ b)) := by
    apply le_antisymm
    · apply ciSup_le
      intro J
      apply Finite.le_ciSup_of_le J
      have hb : BddAbove (Set.range fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦
          (s ω).ϕ (τ (∏ σ ∈ J.val, σ b))) := ⟨P ω, by
        rintro _ ⟨τ, rfl⟩
        exact hbound ω J τ⟩
      apply le_ciSup_of_le hb (AlgEquiv.refl : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      change (∏ σ ∈ J.val, (s ω).ϕ (σ b)) ≤ (s ω).ϕ (∏ σ ∈ J.val, σ b)
      rw [AbsoluteValue.map_prod]
    · apply ciSup_le
      intro J
      exact ciSup_le (hbound ω J)
  change Measurable fun ω ↦ P ω
  simp_rw [heq]
  apply Measurable.iSup
  intro J
  apply measurable_iSup_abv_aut AS s hs
  change (∏ σ ∈ J.val, σ b) ∈ separableClosure K (AlgebraicClosure K)
  exact (separableClosure K (AlgebraicClosure K)).prod_mem
    (fun σ _ ↦ IsSeparable.map σ σ.injective (Algebra.IsSeparable.isSeparable K b))

variable (K) in
/-- The decreasingly ordered absolute values of the embeddings of a nonzero separable
element are measurable. The chosen ordering need not depend measurably on the base point. -/
theorem measurable_ordered_abv_embeddings {E : Type*} [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (s : AS.Ω → ParameterSpaceExtension AS (AlgebraicClosure K))
    (hs : ∀ ω, (s ω).proj = ω) (b : E) (hb : b ≠ 0)
    {n : ℕ} (e : Fin n ≃ (E →ₐ[K] AlgebraicClosure K))
    (π : AS.Ω → Equiv.Perm (Fin n))
    (hπ : ∀ ω, Antitone (fun i ↦ (s ω).ϕ (e (π ω i) b)))
    (i : Fin n) :
    Measurable fun ω ↦ (s ω).ϕ (e (π ω i) b) := by
  classical
  have hP (k : ℕ) (hk : k ≤ n) :
      Measurable fun ω ↦
        ⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, (s ω).ϕ (e j b) := by
    let eJ := e.finsetCongr.subtypeEquiv
      (p := fun J : Finset (Fin n) ↦ J.card = k)
      (q := fun J : Finset (E →ₐ[K] AlgebraicClosure K) ↦ J.card = k)
      (by intro J; simp)
    have heq (ω : AS.Ω) :
        (⨆ J : {J : Finset (Fin n) // J.card = k}, ∏ j ∈ J.val, (s ω).ϕ (e j b)) =
        ⨆ J : {J : Finset (E →ₐ[K] AlgebraicClosure K) // J.card = k},
          ∏ σ ∈ J.val, (s ω).ϕ (σ b) := by
      calc
        _ = ⨆ J : {J : Finset (Fin n) // J.card = k},
            ∏ σ ∈ (eJ J).val, (s ω).ϕ (σ b) := by
          apply iSup_congr
          intro J
          simp [eJ, Equiv.subtypeEquiv, Finset.prod_map]
        _ = _ := eJ.iSup_comp (g := fun J ↦ ∏ σ ∈ J.val, (s ω).ϕ (σ b))
    simp_rw [heq]
    apply measurable_iSup_prod_embeddings (AS := AS) K s hs b k
    simpa only [← Fintype.card_congr e, Fintype.card_fin] using hk
  exact measurable_perm_eval_of_measurable_iSup_prod
    (fun ω i ↦ (s ω).ϕ (e i b))
    (fun ω i ↦ (s ω).ϕ.pos ((map_ne_zero (e i)).mpr hb)) π hπ hP i

variable (K) in
/-- The sum of the absolute values of all embeddings of an element of a finite separable
extension is measurable for any choice of extensions to the algebraic closure. -/
theorem measurable_sum_abv_embeddings {E : Type*} [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (s : AS.Ω → ParameterSpaceExtension AS (AlgebraicClosure K))
    (hs : ∀ ω, (s ω).proj = ω) (b : E) :
    Measurable fun ω ↦ ∑ σ : E →ₐ[K] AlgebraicClosure K, (s ω).ϕ (σ b) := by
  classical
  by_cases hb : b = 0
  · simp only [hb, map_zero, Finset.sum_const_zero]
    exact measurable_const
  let n := Fintype.card (E →ₐ[K] AlgebraicClosure K)
  let e : Fin n ≃ (E →ₐ[K] AlgebraicClosure K) := (Fintype.equivFin _).symm
  let x (ω : AS.Ω) (i : Fin n) := (s ω).ϕ (e i b)
  let π (ω : AS.Ω) := Tuple.sort (α := ℝᵒᵈ) (fun i ↦ x ω i)
  have hπ (ω : AS.Ω) : Antitone (x ω ∘ π ω) :=
    Tuple.monotone_sort (α := ℝᵒᵈ) (fun i ↦ x ω i)
  have hm (i : Fin n) : Measurable fun ω ↦ x ω (π ω i) :=
    measurable_ordered_abv_embeddings (AS := AS) K s hs b hb e π hπ i
  have heq (ω : AS.Ω) : (∑ σ : E →ₐ[K] AlgebraicClosure K, (s ω).ϕ (σ b)) =
      ∑ i : Fin n, x ω (π ω i) := by
    rw [Equiv.sum_comp (π ω)]
    exact (e.sum_comp (fun σ ↦ (s ω).ϕ (σ b))).symm
  simp_rw [heq]
  exact Finset.measurable_sum _ (fun i _ ↦ hm i)

end ArakelovGeometry.AdelicStructure

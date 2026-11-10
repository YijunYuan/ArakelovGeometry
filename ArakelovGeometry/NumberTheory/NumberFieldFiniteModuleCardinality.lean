/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.Algebra.BigOperators.Finprod

/-! # Cardinality of a finite number-field integer module from local lengths -/

noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

namespace ArakelovGeometry.NumberFieldFiniteModule

universe u v

variable {K : Type u} [Field K] [NumberField K]

open Classical in
/-- A residue-field factor survives precisely at its own actual prime. -/
theorem length_tensor_residue (p q : HeightOneSpectrum (𝓞 K))
    (S : Type*) [CommRing S] [Algebra (𝓞 K) S]
    [IsLocalization p.asIdeal.primeCompl S] :
    Module.length S (S ⊗[𝓞 K] (𝓞 K ⧸ q.asIdeal)) = if p = q then 1 else 0 := by
  classical
  let := IsLocalization.AtPrime.isLocalRing S p.asIdeal
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S q.asIdeal).toLinearEquiv.length_eq]
  by_cases h : p = q
  · subst q
    rw [if_pos rfl, IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal S]
    have : IsSimpleModule S (S ⧸ IsLocalRing.maximalIdeal S) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
    exact Module.length_eq_one S (S ⧸ IsLocalRing.maximalIdeal S)
  · rw [if_neg h]
    have hle : ¬ q.asIdeal ≤ p.asIdeal := by
      intro hle
      apply h
      exact HeightOneSpectrum.ext (q.isMaximal.eq_of_le p.isPrime.ne_top hle).symm
    obtain ⟨a, haq, hap⟩ := SetLike.not_le_iff_exists.mp hle
    have htop : q.asIdeal.map (algebraMap (𝓞 K) S) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haq)
        (IsLocalization.map_units S (⟨a, hap⟩ : p.asIdeal.primeCompl))
    rw [htop]
    exact Module.length_eq_zero

omit [NumberField K] in
/-- Flat scalar extension preserves the additive length identity for the literal quotient. -/
theorem length_tensor_eq_add (S : Type*) [CommRing S] [Algebra (𝓞 K) S]
    [Module.Flat (𝓞 K) S] {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    (N : Submodule (𝓞 K) M) :
    Module.length S (S ⊗[𝓞 K] M) =
      Module.length S (S ⊗[𝓞 K] N) + Module.length S (S ⊗[𝓞 K] (M ⧸ N)) := by
  open TensorProduct in
  exact Module.length_eq_add_of_exact
    (AlgebraTensorModule.lTensor S S N.subtype) (AlgebraTensorModule.lTensor S S N.mkQ)
    (Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.subtype_injective)
    (LinearMap.lTensor_surjective S N.mkQ_surjective)
    (Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ N))

open Classical in
/-- The same actual prime list computes cardinality and every localized length.
The coefficient ring may be any genuine prime localization, in particular the
literal rational local coefficient ring used by actual full lattices. -/
theorem exists_primeFactors_of_finiteLength {M : Type v} [AddCommGroup M] [Module (𝓞 K) M]
    (hM : IsFiniteLength (𝓞 K) M) :
    ∃ P : List (HeightOneSpectrum (𝓞 K)),
      Nat.card M = (P.map fun p => Ideal.absNorm p.asIdeal).prod ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)) (S : Type u) [CommRing S] [Algebra (𝓞 K) S]
        [IsLocalization p.asIdeal.primeCompl S],
        Module.length S (S ⊗[𝓞 K] M) = (P.count p : ℕ∞) := by
  induction hM with
  | of_subsingleton =>
    refine ⟨[], ?_, ?_⟩
    · simp
    · intro p S _ _ _
      simp
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨P, hcard, hlength⟩ := ih
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
      (inferInstance : IsSimpleModule (𝓞 K) (M ⧸ N))
    let q : HeightOneSpectrum (𝓞 K) :=
      ⟨I, hI.isPrime, (I.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'⟩
    refine ⟨q :: P, ?_, ?_⟩
    · rw [Submodule.card_eq_card_quotient_mul_card N, hcard,
        Nat.card_congr e.toEquiv]
      change _ * Ideal.absNorm I = _
      simp [q, mul_comm]
    · intro p S _ _ _
      let : Module.Flat (𝓞 K) S := IsLocalization.flat S p.asIdeal.primeCompl
      rw [length_tensor_eq_add S N, hlength p S,
        (LinearEquiv.baseChange (𝓞 K) S _ _ e).length_eq,
        length_tensor_residue p q S]
      simp only [List.count_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      split_ifs <;> simp_all [add_comm]

open Classical in
/-- A finite integer module has a single finite list of actual primes which
computes its cardinality and all its actual prime-local lengths. -/
theorem exists_primeFactors (M : Type v) [AddCommGroup M] [Module (𝓞 K) M] [Finite M] :
    ∃ P : List (HeightOneSpectrum (𝓞 K)),
      Nat.card M = (P.map fun p => Ideal.absNorm p.asIdeal).prod ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)) (S : Type u) [CommRing S] [Algebra (𝓞 K) S]
        [IsLocalization p.asIdeal.primeCompl S],
        Module.length S (S ⊗[𝓞 K] M) = (P.count p : ℕ∞) :=
  exists_primeFactors_of_finiteLength
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

open Classical in
/-- Group a finite prime-factor list without making a finiteness convention
about an infinite product. -/
theorem list_prod_absNorm_eq_finprod (P : List (HeightOneSpectrum (𝓞 K))) :
    (P.map fun p => Ideal.absNorm p.asIdeal).prod =
      ∏ᶠ p, Ideal.absNorm p.asIdeal ^ P.count p := by
  classical
  rw [finprod_eq_finsetProd_of_mulSupport_subset (s := P.toFinset)]
  · exact Finset.prod_list_map_count P (fun p => Ideal.absNorm p.asIdeal)
  · intro p hp
    by_contra h
    have hc : P.count p = 0 := List.count_eq_zero_of_not_mem (by simpa using h)
    exact hp (by simp [hc])

end ArakelovGeometry.NumberFieldFiniteModule

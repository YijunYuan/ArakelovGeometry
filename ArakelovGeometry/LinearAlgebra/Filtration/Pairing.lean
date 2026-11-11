/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.Graded
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Intrinsic numerical invariants of real filtrations

The dimensions of the actual graded subquotients determine the expectation.
Adapted bases compute these dimensions by counting their weights.
-/

@[expose] public section

open Module

namespace Submodule

variable {K E ι : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Intersections of coordinate subspaces use the intersection of the index sets. -/
theorem span_basis_image_inf (b : Basis ι K E) (s t : Set ι) :
    span K (b '' s) ⊓ span K (b '' t) = span K (b '' (s ∩ t)) := by
  ext x
  simp only [mem_inf, b.mem_span_image, Set.subset_inter_iff]

/-- Strict cuts of a weighted spanning family are obtained by strict inequalities. -/
theorem filtrationRightLimit_eq_span_weights (b : ι → E) (a : ι → ℝ)
    {F : ℝ → Submodule K E}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ a i})) (t : ℝ) :
    filtrationRightLimit F t = span K (b '' {i | t < a i}) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    rw [hF]
    exact span_mono (Set.image_mono (fun i hi ↦ s.property.trans_le hi))
  · apply span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    apply (le_iSup (fun s : {s : ℝ // t < s} ↦ F s.val) ⟨a i, hi⟩)
    rw [hF]
    exact subset_span ⟨i, (show a i ≤ a i from le_rfl), rfl⟩

/-- The dimension of a coordinate subspace is the number of its basis indices. -/
theorem finrank_span_basis_image [Fintype ι] (b : Basis ι K E) (p : ι → Prop)
    [DecidablePred p] :
    finrank K (span K (b '' {i | p i})) = (Finset.univ.filter p).card := by
  have he : b '' {i | p i} = Set.range (fun i : {i // p i} ↦ b i) := by
    ext x
    simp
  rw [he]
  exact (finrank_span_eq_card (b.linearIndependent.comp
    (fun i : {i // p i} ↦ (i : ι)) Subtype.val_injective)).trans (Fintype.card_subtype p)

variable [Fintype ι] [FiniteDimensional K E]

/-- The actual quotient grade has one dimension for each basis weight equal to its level. -/
theorem finrank_filtrationGraded_eq_card (b : Basis ι K E) (a : ι → ℝ)
    {F : ℝ → Submodule K E}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ a i})) (t : ℝ) :
    finrank K (FiltrationGraded F t) = (Finset.univ.filter fun i ↦ a i = t).card := by
  classical
  have hanti : Antitone F := by
    intro s t hst
    rw [hF, hF]
    exact span_mono (Set.image_mono (fun _ hi ↦ hst.trans hi))
  rw [finrank_quotient,
    (comapSubtypeEquivOfLe (filtrationRightLimit_le hanti t)).finrank_eq,
    filtrationRightLimit_eq_span_weights b a hF, hF,
    finrank_span_basis_image, finrank_span_basis_image]
  have hc : (Finset.univ.filter fun i ↦ t ≤ a i).card =
      (Finset.univ.filter fun i ↦ t < a i).card +
        (Finset.univ.filter fun i ↦ a i = t).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      exact le_iff_lt_or_eq.trans (or_congr_right eq_comm)
    · apply Finset.disjoint_left.mpr
      intro i hi hj
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      exact (ne_of_gt hi') hj'
  omega

omit [Fintype ι] in
/-- The intrinsic nonzero-grade support is exactly the set of adapted-basis weights. -/
theorem support_finrank_filtrationGraded [Finite ι] (b : Basis ι K E) (a : ι → ℝ)
    {F : ℝ → Submodule K E}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ a i})) :
    Function.support (fun t ↦ finrank K (FiltrationGraded F t)) = Set.range a := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  ext t
  simp only [Function.mem_support, finrank_filtrationGraded_eq_card b a hF,
    Finset.card_ne_zero, Finset.filter_nonempty_iff, Finset.mem_univ, true_and,
    Set.mem_range]

omit [Fintype ι] in
/-- All actual nonzero grades occur at finitely many adapted weights. -/
theorem finite_support_finrank_filtrationGraded [Finite ι] (b : Basis ι K E) (a : ι → ℝ)
    {F : ℝ → Submodule K E}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ a i})) :
    (Function.support (fun t ↦ finrank K (FiltrationGraded F t))).Finite := by
  rw [support_finrank_filtrationGraded b a hF]
  exact Set.finite_range a

/-- The dimension-weighted sum of actual grades equals the sum of arbitrary adapted weights. -/
theorem finsum_weight_mul_finrank_filtrationGraded (b : Basis ι K E) (a : ι → ℝ)
    {F : ℝ → Submodule K E}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ a i})) :
    (∑ᶠ t : ℝ, t * (finrank K (FiltrationGraded F t) : ℝ)) = ∑ i, a i := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image a) (by
    intro t ht
    have hn : finrank K (FiltrationGraded F t) ≠ 0 := by
      intro hz
      exact ht (by simp [hz])
    have hm : t ∈ Set.range a := (support_finrank_filtrationGraded b a hF) ▸ hn
    simpa using hm)]
  simp_rw [finrank_filtrationGraded_eq_card b a hF]
  have he := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset ι)) (t := Finset.univ.image a)
    (g := a) (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩) (fun t : ℝ ↦ t)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using he

omit [Fintype ι] in
/-- Intrinsic expectation of a real filtration, normalized by dimension.
For genuine finite filtrations the sum has finite support. Rank zero gives zero. -/
noncomputable def filtrationExpectation (F : ℝ → Submodule K E) : ℝ :=
  (∑ᶠ t : ℝ, t * (finrank K (FiltrationGraded F t) : ℝ)) / finrank K E

/-- Every finite adapted basis computes the same intrinsic expectation. -/
theorem filtrationExpectation_eq_sum_weights (b : Basis ι K E) (a : ι → ℝ)
    {F : ℝ → Submodule K E}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ a i})) :
    filtrationExpectation F = (∑ i, a i) / finrank K E := by
  rw [filtrationExpectation, finsum_weight_mul_finrank_filtrationGraded b a hF]

omit [Fintype ι] in
/-- A flag reconstruction has no nonzero actual grade outside its recorded jumps. -/
theorem finrank_filtrationGraded_eq_zero_of_flag
    {F : ℝ → Submodule K E} {n : ℕ}
    (U : Fin (n + 1) → Submodule K E) (a : Fin n → ℝ)
    (hlevel : ∀ i, F (a i) = U i.succ)
    (hrec : ∀ t, F t = ⨆ (i : Fin n) (_ : t ≤ a i), U i.succ)
    {t : ℝ} (ht : t ∉ Set.range a) : finrank K (FiltrationGraded F t) = 0 := by
  have hle : F t ≤ filtrationRightLimit F t := by
    rw [hrec]
    refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
    have hlt : t < a i := lt_of_le_of_ne hi (fun he ↦ ht ⟨i, he.symm⟩)
    rw [← hlevel i]
    exact le_iSup (fun s : {s : ℝ // t < s} ↦ F s.val) ⟨a i, hlt⟩
  have he : (filtrationRightLimit F t).comap (F t).subtype = ⊤ :=
    top_unique (fun x _ ↦ hle x.property)
  change finrank K (F t ⧸ (filtrationRightLimit F t).comap (F t).subtype) = 0
  rw [he, finrank_quotient, finrank_top, Nat.sub_self]

omit [Fintype ι] in
/-- The intrinsic weighted graded sum can be computed on any distinct-jump flag. -/
theorem finsum_weight_mul_finrank_filtrationGraded_eq_flag
    {F : ℝ → Submodule K E} {n : ℕ}
    (U : Fin (n + 1) → Submodule K E) (a : Fin n → ℝ)
    (ha : Function.Injective a)
    (hlevel : ∀ i, F (a i) = U i.succ)
    (hright : ∀ i, filtrationRightLimit F (a i) = U i.castSucc)
    (hrec : ∀ t, F t = ⨆ (i : Fin n) (_ : t ≤ a i), U i.succ) :
    (∑ᶠ t : ℝ, t * (finrank K (FiltrationGraded F t) : ℝ)) =
      ∑ i : Fin n, a i *
        (finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype) : ℝ) := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image a) (by
    intro t ht
    by_contra hn
    have hn' : t ∉ Set.range a := by simpa using hn
    exact ht (by simp only [finrank_filtrationGraded_eq_zero_of_flag U a hlevel hrec hn',
      Nat.cast_zero, mul_zero]))]
  rw [Finset.sum_image (fun i _ j _ h ↦ ha h)]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [FiltrationGraded]
  rw [hright, hlevel]

omit [Fintype ι] in
/-- Joint multiplicity from intrinsic intersection dimensions. For decreasing
filtrations this is the codimension of the sum of the two strict intersections. -/
noncomputable def filtrationJointMultiplicity (F G : ℝ → Submodule K E) (s t : ℝ) : ℕ :=
  finrank K ↥(F s ⊓ G t) -
    finrank K ↥((filtrationRightLimit F s ⊓ G t) ⊔ (F s ⊓ filtrationRightLimit G t))

omit [Fintype ι] in
/-- The intersection formula is the dimension of its actual joint subquotient. -/
theorem filtrationJointMultiplicity_eq_finrank_quotient
    {F G : ℝ → Submodule K E} (hF : Antitone F) (hG : Antitone G) (s t : ℝ) :
    filtrationJointMultiplicity F G s t =
      finrank K (↥(F s ⊓ G t) ⧸
        ((filtrationRightLimit F s ⊓ G t) ⊔ (F s ⊓ filtrationRightLimit G t)).comap
          (F s ⊓ G t).subtype) := by
  have hle : (filtrationRightLimit F s ⊓ G t) ⊔ (F s ⊓ filtrationRightLimit G t) ≤
      F s ⊓ G t :=
    sup_le (inf_le_inf_right _ (filtrationRightLimit_le hF s))
      (inf_le_inf_left _ (filtrationRightLimit_le hG t))
  rw [finrank_quotient, (comapSubtypeEquivOfLe hle).finrank_eq]
  rfl

omit [FiniteDimensional K E] in
/-- Joint intrinsic multiplicities count exactly the pairs of common adapted weights. -/
theorem filtrationJointMultiplicity_eq_card (b : Basis ι K E) (a c : ι → ℝ)
    {F G : ℝ → Submodule K E}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ a i}))
    (hG : ∀ t, G t = span K (b '' {i | t ≤ c i})) (s t : ℝ) :
    filtrationJointMultiplicity F G s t =
      (Finset.univ.filter fun i ↦ a i = s ∧ c i = t).card := by
  classical
  unfold filtrationJointMultiplicity
  rw [filtrationRightLimit_eq_span_weights b a hF,
    filtrationRightLimit_eq_span_weights b c hG, hF, hG,
    span_basis_image_inf, span_basis_image_inf, span_basis_image_inf,
    ← span_union, ← Set.image_union]
  change finrank K (span K (b '' {i | s ≤ a i ∧ t ≤ c i})) -
    finrank K (span K (b '' {i | (s < a i ∧ t ≤ c i) ∨ (s ≤ a i ∧ t < c i)})) = _
  rw [finrank_span_basis_image, finrank_span_basis_image]
  have hsub :
      (Finset.univ.filter fun i ↦ (s < a i ∧ t ≤ c i) ∨ (s ≤ a i ∧ t < c i)) ⊆
        (Finset.univ.filter fun i ↦ s ≤ a i ∧ t ≤ c i) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases (Finset.mem_filter.mp hi).2 with h | h
    · exact ⟨h.1.le, h.2⟩
    · exact ⟨h.1, h.2.le⟩
  rw [← Finset.card_sdiff_of_subset hsub]
  congr 1
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hi, hj⟩, hn⟩
    exact ⟨le_antisymm (le_of_not_gt (fun h ↦ hn (Or.inl ⟨h, hj⟩))) hi,
      le_antisymm (le_of_not_gt (fun h ↦ hn (Or.inr ⟨hi, h⟩))) hj⟩
  · rintro ⟨hi, hj⟩
    simp [hi, hj]

omit [Fintype ι] in
/-- Basis-independent pairing, normalized by the ambient dimension and defined
using only actual filtration intersections and strict cuts. -/
noncomputable def filtrationPairing (F G : ℝ → Submodule K E) : ℝ :=
  (∑ᶠ p : ℝ × ℝ, p.1 * p.2 * (filtrationJointMultiplicity F G p.1 p.2 : ℝ)) /
    finrank K E

omit [FiniteDimensional K E] in
/-- Every common adapted basis computes the same normalized intrinsic pairing. -/
theorem filtrationPairing_eq_sum_weights (b : Basis ι K E) (a c : ι → ℝ)
    {F G : ℝ → Submodule K E}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ a i}))
    (hG : ∀ t, G t = span K (b '' {i | t ≤ c i})) :
    filtrationPairing F G = (∑ i, a i * c i) / finrank K E := by
  classical
  let w : ι → ℝ × ℝ := fun i ↦ (a i, c i)
  have hm (p : ℝ × ℝ) : filtrationJointMultiplicity F G p.1 p.2 =
      (Finset.univ.filter fun i ↦ w i = p).card := by
    rw [filtrationJointMultiplicity_eq_card b a c hF hG]
    congr 1
  unfold filtrationPairing
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image w) (by
    intro p hp
    by_contra hn
    have hz : (Finset.univ.filter fun i ↦ w i = p) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
    exact hp (by simp only [hm, hz, Finset.card_empty, Nat.cast_zero, mul_zero]))]
  simp_rw [hm]
  have he := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset ι)) (t := Finset.univ.image w)
    (g := w) (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun p : ℝ × ℝ ↦ p.1 * p.2)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using he

omit [Fintype ι] [FiniteDimensional K E] in
/-- The joint multiplicities have precisely the finite support of common weight pairs. -/
theorem support_filtrationJointMultiplicity [Finite ι]
    (b : Basis ι K E) (a c : ι → ℝ) {F G : ℝ → Submodule K E}
    (hF : ∀ t, F t = span K (b '' {i | t ≤ a i}))
    (hG : ∀ t, G t = span K (b '' {i | t ≤ c i})) :
    Function.support (fun p : ℝ × ℝ ↦ filtrationJointMultiplicity F G p.1 p.2) =
      Set.range (fun i ↦ (a i, c i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  ext p
  simp only [Function.mem_support, filtrationJointMultiplicity_eq_card b a c hF hG,
    Finset.card_ne_zero, Finset.filter_nonempty_iff, Finset.mem_univ, true_and,
    Set.mem_range, Prod.ext_iff]

omit [Fintype ι] [FiniteDimensional K E] in
/-- The other filtration induces cuts on the actual shared graded quotient. -/
noncomputable def filtrationOnGraded (F G : ℝ → Submodule K E) (s t : ℝ) :
    Submodule K (FiltrationGraded F s) :=
  ((G t).comap (F s).subtype).map (filtrationGradedMk F s)

omit [Fintype ι] [FiniteDimensional K E] in
theorem antitone_filtrationOnGraded (F : ℝ → Submodule K E)
    {G : ℝ → Submodule K E} (hG : Antitone G) (s : ℝ) :
    Antitone (filtrationOnGraded F G s) := by
  intro u v huv
  exact map_mono (comap_mono (hG huv))

omit [Fintype ι] [FiniteDimensional K E] in
theorem filtrationRightLimit_comap {V : Type*} [AddCommGroup V] [Module K V]
    {G : ℝ → Submodule K E} (hG : Antitone G) (f : V →ₗ[K] E) (t : ℝ) :
    filtrationRightLimit (fun u ↦ (G u).comap f) t = (filtrationRightLimit G t).comap f := by
  let : Nonempty {u : ℝ // t < u} := ⟨⟨t + 1, lt_add_one t⟩⟩
  have hd : Directed (· ≤ ·) (fun u : {u : ℝ // t < u} ↦ G u.val) := by
    intro u v
    exact ⟨⟨min u.val v.val, lt_min u.property v.property⟩,
      hG (min_le_left _ _), hG (min_le_right _ _)⟩
  have hd' : Directed (· ≤ ·) (fun u : {u : ℝ // t < u} ↦ (G u.val).comap f) := by
    intro u v
    obtain ⟨w, huw, hvw⟩ := hd u v
    exact ⟨w, comap_mono huw, comap_mono hvw⟩
  ext x
  simp only [filtrationRightLimit, mem_iSup_of_directed _ hd', mem_comap,
    mem_iSup_of_directed _ hd]

omit [Fintype ι] [FiniteDimensional K E] in
theorem filtrationRightLimit_filtrationOnGraded (F : ℝ → Submodule K E)
    {G : ℝ → Submodule K E} (hG : Antitone G) (s t : ℝ) :
    filtrationRightLimit (filtrationOnGraded F G s) t =
      ((filtrationRightLimit G t).comap (F s).subtype).map (filtrationGradedMk F s) := by
  change (⨆ u : {u : ℝ // t < u}, ((G u.val).comap (F s).subtype).map
    (filtrationGradedMk F s)) = _
  rw [← map_iSup]
  rw [← filtrationRightLimit_comap hG (F s).subtype t]
  rfl

omit [Fintype ι] [FiniteDimensional K E] in
theorem finrank_comap_subtype (A B : Submodule K E) :
    finrank K (B.comap A.subtype) = finrank K ↥(A ⊓ B) := by
  rw [← finrank_map_subtype_eq A (B.comap A.subtype), map_comap_subtype]

omit [Fintype ι] in
theorem finrank_map_mkQ (P Q : Submodule K E) :
    finrank K (P.map Q.mkQ) = finrank K P - finrank K ↥(P ⊓ Q) := by
  have h := (Q.mkQ.comp P.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp, range_subtype, LinearMap.ker_comp, ker_mkQ,
    finrank_comap_subtype] at h
  omega

omit [Fintype ι] in
theorem finrank_map_filtrationGradedMk {F : ℝ → Submodule K E}
    (hF : Antitone F) (B : Submodule K E) (s : ℝ) :
    finrank K ((B.comap (F s).subtype).map (filtrationGradedMk F s)) =
      finrank K ↥(F s ⊓ B) - finrank K ↥(filtrationRightLimit F s ⊓ B) := by
  change finrank K ((B.comap (F s).subtype).map
    ((filtrationRightLimit F s).comap (F s).subtype).mkQ) = _
  rw [finrank_map_mkQ, ← comap_inf, finrank_comap_subtype, finrank_comap_subtype]
  have he : F s ⊓ (B ⊓ filtrationRightLimit F s) = filtrationRightLimit F s ⊓ B := by
    rw [inf_comm B, ← inf_assoc, inf_eq_right.mpr (filtrationRightLimit_le hF s)]
  rw [he]

omit [Fintype ι] in
/-- The intrinsic joint multiplicity is the dimension of the actual iterated grade. -/
theorem finrank_filtrationGraded_filtrationOnGraded
    {F G : ℝ → Submodule K E} (hF : Antitone F) (hG : Antitone G) (s t : ℝ) :
    finrank K (FiltrationGraded (filtrationOnGraded F G s) t) =
      filtrationJointMultiplicity F G s t := by
  change finrank K ((filtrationOnGraded F G s t) ⧸
    (filtrationRightLimit (filtrationOnGraded F G s) t).comap
      (filtrationOnGraded F G s t).subtype) = _
  rw [finrank_quotient,
    (comapSubtypeEquivOfLe (filtrationRightLimit_le (antitone_filtrationOnGraded F hG s) t)).finrank_eq,
    filtrationRightLimit_filtrationOnGraded F hG]
  change finrank K (((G t).comap (F s).subtype).map (filtrationGradedMk F s)) - _ = _
  rw [finrank_map_filtrationGradedMk hF, finrank_map_filtrationGradedMk hF]
  have hFs := filtrationRightLimit_le hF s
  have hGt := filtrationRightLimit_le hG t
  have hBC : (filtrationRightLimit F s ⊓ G t) ⊓ (F s ⊓ filtrationRightLimit G t) =
      filtrationRightLimit F s ⊓ filtrationRightLimit G t := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
    · exact le_inf (inf_le_inf le_rfl hGt) (inf_le_inf hFs le_rfl)
  have hd := finrank_sup_add_finrank_inf_eq
    (filtrationRightLimit F s ⊓ G t) (F s ⊓ filtrationRightLimit G t)
  rw [hBC] at hd
  have hle : (filtrationRightLimit F s ⊓ G t) ⊔ (F s ⊓ filtrationRightLimit G t) ≤
      F s ⊓ G t := sup_le (inf_le_inf hFs le_rfl) (inf_le_inf le_rfl hGt)
  have hr := finrank_mono hle
  have hDC := finrank_mono (inf_le_inf hFs (le_refl (filtrationRightLimit G t)))
  unfold filtrationJointMultiplicity
  omega

end Submodule

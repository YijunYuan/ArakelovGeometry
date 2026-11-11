/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.ImageHN
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Tensor
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HNOptimalVariation

/-!
# Binary graded tensor images in Bost's degree argument

The source bundles are actual binary tensors of actual grades. Their maps
to the original quotient grade are the canonical A5 maps. The finite-image
HN inequality consumes the proved completed contractions directly.
-/

@[expose] public section

open scoped TensorProduct BigOperators
open Module

namespace Submodule

variable {K E V Q : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Q] [Module K Q]
  {P : ℝ → Submodule K E} {R : ℝ → Submodule K V}

/-- The exact canonical A5 pair followed by its canonical quotient-grade map.
This abbreviation does not change the carrier or choose an image norm. -/
noncomputable abbrev tensorFiltrationGradedQuotientPair
    (q : E ⊗[K] V →ₗ[K] Q) (hP : Antitone P) (hR : Antitone R)
    {t u γ : ℝ} (h : t + u = γ) :
    FiltrationGraded P t ⊗[K] FiltrationGraded R u →ₗ[K]
      FiltrationGraded (fun s ↦ (tensorFiltration P R s).map q) γ :=
  (filtrationGradedMap q (fun s ↦ le_comap_map q (tensorFiltration P R s)) γ).comp
    (tensorFiltrationGradedPair hP hR h)

/-- Only finitely many actual pair grades are needed to span a quotient
grade. Repeated basis weights retain repeated copies of the same canonical
pair map, which does not affect their common image. -/
theorem iSup_range_tensorFiltrationGradedQuotientPair
    {ι κ : Type*} [Finite ι] [Finite κ]
    (b : Basis ι K E) (c : Basis κ K V) (w : ι → ℝ) (z : κ → ℝ)
    (q : E ⊗[K] V →ₗ[K] Q) (hP : Antitone P) (hR : Antitone R)
    (hPw : ∀ t, P t = span K (b '' {i | t ≤ w i}))
    (hRz : ∀ u, R u = span K (c '' {j | u ≤ z j})) (γ : ℝ) :
    (⨆ p : {ij : ι × κ // w ij.1 + z ij.2 = γ},
      (tensorFiltrationGradedQuotientPair q hP hR p.property).range) = ⊤ := by
  classical
  let M := ⨆ p : {ij : ι × κ // w ij.1 + z ij.2 = γ},
    (tensorFiltrationGradedQuotientPair q hP hR p.property).range
  have hm (p : {p : ℝ × ℝ // p.1 + p.2 = γ})
      (x : FiltrationGraded P p.val.1 ⊗[K] FiltrationGraded R p.val.2) :
      tensorFiltrationGradedQuotientPair q hP hR p.property x ∈ M := by
    rcases p with ⟨⟨t, u⟩, hp⟩
    by_cases ht : t ∈ Set.range w
    · obtain ⟨i, rfl⟩ := ht
      by_cases hu : u ∈ Set.range z
      · obtain ⟨j, rfl⟩ := hu
        exact (le_iSup (fun p : {ij : ι × κ // w ij.1 + z ij.2 = γ} ↦
          (tensorFiltrationGradedQuotientPair q hP hR p.property).range) ⟨(i, j), hp⟩) ⟨x, rfl⟩
      · have hz : Module.finrank K (FiltrationGraded R u) = 0 := by
          by_contra hn
          exact hu ((support_finrank_filtrationGraded c z hRz) ▸ hn)
        have hr : Module.finrank K (FiltrationGraded P (w i) ⊗[K] FiltrationGraded R u) = 0 := by
          rw [Module.finrank_tensorProduct, hz, mul_zero]
        have := (Module.finrank_eq_zero_iff_of_free K _).mp hr
        rw [Subsingleton.elim x 0, map_zero]
        exact M.zero_mem
    · have hz : Module.finrank K (FiltrationGraded P t) = 0 := by
        by_contra hn
        exact ht ((support_finrank_filtrationGraded b w hPw) ▸ hn)
      have hr : Module.finrank K (FiltrationGraded P t ⊗[K] FiltrationGraded R u) = 0 := by
        rw [Module.finrank_tensorProduct, hz, zero_mul]
      have := (Module.finrank_eq_zero_iff_of_free K _).mp hr
      rw [Subsingleton.elim x 0, map_zero]
      exact M.zero_mem
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨x, rfl⟩ := tensorFiltrationGradedQuotient_surjective q b c w z hP hR hPw hRz γ y
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using M.add_mem hx hy
  | of p x =>
    rw [← DirectSum.lof_eq_of K]
    simpa only [tensorFiltrationGradedQuotient, LinearMap.comp_apply,
      tensorFiltrationGradedSum, DirectSum.toModule_lof] using hm p x

section SecondaryCoordinates

variable {ι κ : Type*} (b : ι → E) (c : κ → V) (w : ι → ℝ) (z : κ → ℝ)
  (hb : ∀ i, b i ∈ P (w i)) (hc : ∀ j, c j ∈ R (z j))

omit [FiniteDimensional K E] in
/-- The class of a prescribed primary-weight generator in its actual grade. -/
noncomputable def filtrationGradedGenerator (t : ℝ) (i : {i : ι // w i = t}) :
    FiltrationGraded P t :=
  filtrationGradedMk P t ⟨b i.val, (congrArg P i.property).le (hb i.val)⟩

/-- The class of an original tensor generator in the actual quotient grade,
expressed through the exact canonical pair composite. -/
noncomputable def tensorQuotientGradedGenerator
    (q : E ⊗[K] V →ₗ[K] Q) (hP : Antitone P) (hR : Antitone R) (γ : ℝ)
    (p : {ij : ι × κ // w ij.1 + z ij.2 = γ}) :
    FiltrationGraded (fun s ↦ (tensorFiltration P R s).map q) γ :=
  tensorFiltrationGradedQuotientPair q hP hR p.property
    (filtrationGradedGenerator b w hb (w p.val.1) ⟨p.val.1, rfl⟩ ⊗ₜ[K]
      filtrationGradedGenerator c z hc (z p.val.2) ⟨p.val.2, rfl⟩)

omit [FiniteDimensional K E] [FiniteDimensional K V] in
/-- The canonical maps identify the secondary image with the literal span
of original tensor classes having the specified primary and secondary
weights. The premises specify the chosen source generators, not an image
filtration or a degree bound. -/
theorem imageFiltration_tensor_secondary_eq_span
    (q : E ⊗[K] V →ₗ[K] Q) (hP : Antitone P) (hR : Antitone R)
    (s : ι → ℝ) (v : κ → ℝ)
    (H : ∀ t, ℝ → Submodule K (FiltrationGraded P t))
    (J : ∀ u, ℝ → Submodule K (FiltrationGraded R u))
    (hH : ∀ t a, H t a = span K
      (filtrationGradedGenerator b w hb t '' {i | a ≤ s i.val}))
    (hJ : ∀ u a, J u a = span K
      (filtrationGradedGenerator c z hc u '' {j | a ≤ v j.val})) (γ ℓ : ℝ) :
    imageFiltration
      (fun p : {ij : ι × κ // w ij.1 + z ij.2 = γ} ↦
        tensorFiltrationGradedQuotientPair q hP hR p.property)
      (fun p ↦ tensorFiltration (H (w p.val.1)) (J (z p.val.2))) ℓ =
    span K (tensorQuotientGradedGenerator b c w z hb hc q hP hR γ ''
      {p | ℓ ≤ s p.val.1 + v p.val.2}) := by
  have he (p : {ij : ι × κ // w ij.1 + z ij.2 = γ})
      (i : {i : ι // w i = w p.val.1}) (j : {j : κ // z j = z p.val.2}) :
      tensorFiltrationGradedQuotientPair q hP hR p.property
        (filtrationGradedGenerator b w hb _ i ⊗ₜ[K] filtrationGradedGenerator c z hc _ j) =
      tensorQuotientGradedGenerator b c w z hb hc q hP hR γ
        ⟨(i.val, j.val), by rw [i.property, j.property]; exact p.property⟩ := by
    rfl
  apply le_antisymm
  · apply iSup_le
    intro p
    dsimp only
    rw [tensorFiltration_eq_span
      (filtrationGradedGenerator b w hb (w p.val.1))
      (filtrationGradedGenerator c z hc (z p.val.2))
      (fun i ↦ s i.val) (fun j ↦ v j.val) (hH (w p.val.1)) (hJ (z p.val.2)), map_span]
    apply span_le.mpr
    rintro _ ⟨_, ⟨⟨i, j⟩, hij, rfl⟩, rfl⟩
    rw [he p i j]
    exact subset_span ⟨⟨(i.val, j.val), by rw [i.property, j.property]; exact p.property⟩, hij, rfl⟩
  · apply span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    apply (le_iSup (fun p : {ij : ι × κ // w ij.1 + z ij.2 = γ} ↦
      (tensorFiltration (H (w p.val.1)) (J (z p.val.2)) ℓ).map
        (tensorFiltrationGradedQuotientPair q hP hR p.property)) p)
    refine ⟨filtrationGradedGenerator b w hb _ ⟨p.val.1, rfl⟩ ⊗ₜ[K]
      filtrationGradedGenerator c z hc _ ⟨p.val.2, rfl⟩, ?_, rfl⟩
    apply tmul_mem_tensorFiltration hp
    · rw [hH]
      exact subset_span ⟨⟨p.val.1, rfl⟩, (show s p.val.1 ≤ s p.val.1 from le_rfl), rfl⟩
    · rw [hJ]
      exact subset_span ⟨⟨p.val.2, rfl⟩, (show v p.val.2 ≤ v p.val.2 from le_rfl), rfl⟩

end SecondaryCoordinates

omit [FiniteDimensional K E] in
/-- A common adapted basis induces the literal equal-primary-weight
generators on the actual grade. This applies to chosen HN lift cuts. -/
theorem filtrationOnGraded_eq_span_generators
    {ι : Type*} (b : Basis ι K E) (w s : ι → ℝ)
    {L : ℝ → Submodule K E}
    (hP : ∀ t, P t = span K (b '' {i | t ≤ w i}))
    (hL : ∀ a, L a = span K (b '' {i | a ≤ s i}))
    (hb : ∀ i, b i ∈ P (w i)) (t a : ℝ) :
    filtrationOnGraded P L t a = span K
      (filtrationGradedGenerator b w hb t '' {i | a ≤ s i.val}) := by
  let C := {i : ι | a ≤ s i ∧ t ≤ w i}
  have hC (i : C) : b i.val ∈ P t := by
    rw [hP]
    exact subset_span ⟨i.val, i.property.2, rfl⟩
  let l : C → P t := fun i ↦ ⟨b i.val, hC i⟩
  have he : (span K (Set.range l)).map (P t).subtype = L a ⊓ P t := by
    have hm : (P t).subtype '' Set.range l = b '' C := by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.val, i.property, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨l ⟨i, hi⟩, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
    rw [map_span, hm, hL, hP, span_basis_image_inf]
    rfl
  have hc : (L a).comap (P t).subtype = span K (Set.range l) := by
    have hh := congrArg (Submodule.comap (P t).subtype) he
    simpa only [comap_map_eq, ker_subtype, sup_bot_eq, comap_inf,
      comap_subtype_self, inf_top_eq] using hh.symm
  rw [filtrationOnGraded, hc, map_span]
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases hi : w i.val = t
    · exact subset_span ⟨⟨i.val, hi⟩, i.property.1, rfl⟩
    · have ht : t < w i.val := lt_of_le_of_ne i.property.2 (Ne.symm hi)
      have hz : filtrationGradedMk P t (l i) = 0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        change b i.val ∈ filtrationRightLimit P t
        rw [filtrationRightLimit_eq_span_weights b w hP]
        exact subset_span ⟨i.val, ht, rfl⟩
      rw [hz]
      exact zero_mem _
  · apply span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact subset_span ⟨l ⟨i.val, hi, i.property.ge⟩,
      ⟨⟨i.val, hi, i.property.ge⟩, rfl⟩, rfl⟩

omit [FiniteDimensional K E] in
/-- A class lying in an induced secondary cut has lexicographically bounded
coordinates in any basis adapted to the primary and lifted filtrations. -/
theorem primary_lt_or_secondary_le_of_graded_mem
    {ι : Type*} (b : Basis ι K E) (w s : ι → ℝ)
    {L : ℝ → Submodule K E}
    (hP : ∀ t, P t = span K (b '' {i | t ≤ w i}))
    (hL : ∀ a, L a = span K (b '' {i | a ≤ s i}))
    {t a : ℝ} (x : P t)
    (hx : filtrationGradedMk P t x ∈ filtrationOnGraded P L t a)
    (i : ι) (hi : b.repr (x : E) i ≠ 0) : t < w i ∨ a ≤ s i := by
  obtain ⟨y, hy, he⟩ := hx
  have hz : (y : E) - (x : E) ∈ filtrationRightLimit P t := by
    exact (show y - x ∈ (filtrationRightLimit P t).comap (P t).subtype from
      (Submodule.Quotient.eq _).mp he)
  by_cases ht : t < w i
  · exact Or.inl ht
  · right
    have hzi : b.repr ((y : E) - (x : E)) i = 0 := by
      rw [filtrationRightLimit_eq_span_weights b w hP] at hz
      exact Finsupp.notMem_support_iff.mp (fun hn ↦ ht (b.mem_span_image.mp hz hn))
    have hni : b.repr (y : E) i ≠ 0 := by
      simp only [map_sub, Finsupp.sub_apply, sub_eq_zero] at hzi
      rw [hzi]
      exact hi
    have hy' : (y : E) ∈ span K (b '' {j | a ≤ s j}) := by
      change (y : E) ∈ L a at hy
      rwa [hL] at hy
    exact b.mem_span_image.mp hy' (Finsupp.mem_support_iff.mpr hni)

end Submodule

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  {Q : Type w'} [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- The actual source bundle of a canonical binary graded pair. This is the
existing Hermitian tensor constructor applied to the actual two grades. -/
noncomputable def tensorFiltrationGradedSource
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (P : ℝ → Submodule K E) (R : ℝ → Submodule K F) (t u : ℝ) :
    AdelicVectorBundle S (Submodule.FiltrationGraded P t ⊗[K] Submodule.FiltrationGraded R u) :=
  (V.filtrationGraded P t hS).orthogonalTensorPair (W.filtrationGraded R u hS) hS hN
    (hV.filtrationGraded P t) (hW.filtrationGraded R u)

theorem tensorFiltrationGradedSource_isHermitian
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (P : ℝ → Submodule K E) (R : ℝ → Submodule K F) (t u : ℝ) :
    (tensorFiltrationGradedSource V W hS hN hV hW P R t u).toNormFamily.IsHermitian hN :=
  orthogonalTensorPair_isHermitian _ _ hS hN _ _

/-- The actual quotient of the original tensor bundle, followed by its
actual image-filtration grade. The target norm is not induced from a pair. -/
noncomputable def tensorFiltrationQuotientGraded
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q)
    (P : ℝ → Submodule K E) (R : ℝ → Submodule K F) (γ : ℝ) :
    AdelicVectorBundle S (Submodule.FiltrationGraded
      (fun s ↦ (Submodule.tensorFiltration P R s).map q) γ) :=
  let T := V.orthogonalTensorPair W hS hN hV hW
  (T.pushforward q hq
    (T.isMeasurable.pushforward_of_discrete_or_countable hS q hq)).filtrationGraded
    (fun s ↦ (Submodule.tensorFiltration P R s).map q) γ hS

theorem tensorFiltrationQuotientGraded_isHermitian
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q)
    (P : ℝ → Submodule K E) (R : ℝ → Submodule K F) (γ : ℝ) :
    (tensorFiltrationQuotientGraded V W hS hN hV hW q hq P R γ).toNormFamily.IsHermitian hN := by
  dsimp only [tensorFiltrationQuotientGraded, filtrationGraded]
  apply NormFamily.IsHermitian.quotient
  apply NormFamily.IsHermitian.restrict
  exact (NormFamily.orthogonalTensorPair_isHermitian
    V.toNormFamily W.toNormFamily hN hV hW).pushforward q hq

variable [S.IsProper]

/-- The actual canonical binary pair family satisfies the finite-image HN
degree bound in each actual quotient grade. Neither spanning nor contraction
is assumed: the A5 quotient-surjectivity theorem and the completed pair
contraction producer discharge both. This is the numerical grade bound of
the adapted Bost Lemma 7.2 route before identifying secondary HN weights. -/
theorem tensorFiltrationQuotientGraded_hnImage_degree_ge
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q)
    {P : ℝ → Submodule K E} {R : ℝ → Submodule K F}
    (hP : Antitone P) (hR : Antitone R)
    {ι κ : Type*} [Finite ι] [Finite κ]
    (b : Basis ι K E) (c : Basis κ K F) (w : ι → ℝ) (z : κ → ℝ)
    (hPw : ∀ t, P t = Submodule.span K (b '' {i | t ≤ w i}))
    (hRz : ∀ u, R u = Submodule.span K (c '' {j | u ≤ z j})) (γ : ℝ) :
    let J := {ij : ι × κ // w ij.1 + z ij.2 = γ}
    let C := fun p : J ↦ tensorFiltrationGradedSource V W hS hN hV hW P R (w p.val.1) (z p.val.2)
    let hC := fun p : J ↦ tensorFiltrationGradedSource_isHermitian V W hS hN hV hW P R
      (w p.val.1) (z p.val.2)
    let g := fun p : J ↦ Submodule.tensorFiltrationGradedQuotientPair q hP hR p.property
    let H := Submodule.imageFiltration g (fun p ↦ (C p).hermitianHNFiltration hS hN (hC p))
    (∑ᶠ t : ℝ, t * (finrank K (Submodule.FiltrationGraded H t) : ℝ)) ≤
      (tensorFiltrationQuotientGraded V W hS hN hV hW q hq P R γ).degree hS hN := by
  dsimp only
  apply finsum_hermitianHN_imageFiltration_le_degree
    (fun p : {ij : ι × κ // w ij.1 + z ij.2 = γ} ↦
      tensorFiltrationGradedSource V W hS hN hV hW P R (w p.val.1) (z p.val.2))
    (tensorFiltrationQuotientGraded V W hS hN hV hW q hq P R γ)
    (fun p ↦ Submodule.tensorFiltrationGradedQuotientPair q hP hR p.property)
    hS hN _ (tensorFiltrationQuotientGraded_isHermitian V W hS hN hV hW q hq P R γ)
    (Submodule.iSup_range_tensorFiltrationGradedQuotientPair b c w z q hP hR hPw hRz γ)
  intro p ω x
  exact NormFamily.tensorFiltrationGradedPair_pushforward_norm_le V.toNormFamily W.toNormFamily
    hN hV hW q hq hP hR p.property ω x

/-- Under the explicitly smaller-rank tensor-HN compatibility induction
boundary, the actual canonical pair images of the tensor-HN secondary
filtrations satisfy Bost's local weighted degree bound. This theorem does
not yet identify those images with a chosen ambient HN lifting's cuts. -/
theorem tensorFiltrationQuotientGraded_secondary_degree_ge
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q)
    {P : ℝ → Submodule K E} {R : ℝ → Submodule K F}
    (hP : Antitone P) (hR : Antitone R)
    {ι κ : Type*} [Finite ι] [Finite κ]
    (b : Basis ι K E) (c : Basis κ K F) (w : ι → ℝ) (z : κ → ℝ)
    (hPw : ∀ t, P t = Submodule.span K (b '' {i | t ≤ w i}))
    (hRz : ∀ u, R u = Submodule.span K (c '' {j | u ≤ z j})) (γ : ℝ)
    (hsmall : ∀ p : {ij : ι × κ // w ij.1 + z ij.2 = γ},
      finrank K (Submodule.FiltrationGraded P (w p.val.1)) +
        finrank K (Submodule.FiltrationGraded R (z p.val.2)) < finrank K E + finrank K F)
    (hInd : ∀ t u,
      finrank K (Submodule.FiltrationGraded P t) + finrank K (Submodule.FiltrationGraded R u) <
        finrank K E + finrank K F →
      (tensorFiltrationGradedSource V W hS hN hV hW P R t u).hermitianHNFiltration hS hN
        (tensorFiltrationGradedSource_isHermitian V W hS hN hV hW P R t u) =
      Submodule.tensorFiltration
        ((V.filtrationGraded P t hS).hermitianHNFiltration hS hN (hV.filtrationGraded P t))
        ((W.filtrationGraded R u hS).hermitianHNFiltration hS hN (hW.filtrationGraded R u))) :
    let J := {ij : ι × κ // w ij.1 + z ij.2 = γ}
    let g := fun p : J ↦ Submodule.tensorFiltrationGradedQuotientPair q hP hR p.property
    let H := Submodule.imageFiltration g (fun p ↦ Submodule.tensorFiltration
      ((V.filtrationGraded P (w p.val.1) hS).hermitianHNFiltration hS hN
        (hV.filtrationGraded P (w p.val.1)))
      ((W.filtrationGraded R (z p.val.2) hS).hermitianHNFiltration hS hN
        (hW.filtrationGraded R (z p.val.2))))
    (∑ᶠ t : ℝ, t * (finrank K (Submodule.FiltrationGraded H t) : ℝ)) ≤
      (tensorFiltrationQuotientGraded V W hS hN hV hW q hq P R γ).degree hS hN := by
  have h := tensorFiltrationQuotientGraded_hnImage_degree_ge V W hS hN hV hW q hq
    hP hR b c w z hPw hRz γ
  have he : (fun p : {ij : ι × κ // w ij.1 + z ij.2 = γ} ↦
      (tensorFiltrationGradedSource V W hS hN hV hW P R
        (w p.val.1) (z p.val.2)).hermitianHNFiltration
          hS hN (tensorFiltrationGradedSource_isHermitian V W hS hN hV hW P R
          (w p.val.1) (z p.val.2))) =
      (fun p : {ij : ι × κ // w ij.1 + z ij.2 = γ} ↦ Submodule.tensorFiltration
        ((V.filtrationGraded P (w p.val.1) hS).hermitianHNFiltration hS hN
          (hV.filtrationGraded P (w p.val.1)))
        ((W.filtrationGraded R (z p.val.2) hS).hermitianHNFiltration hS hN
          (hW.filtrationGraded R (z p.val.2)))) :=
    funext fun p ↦ hInd _ _ (hsmall p)
  dsimp only at h ⊢
  rw [he] at h
  exact h

/-- The actual secondary image in a primary quotient grade, formed from the
tensor products of the actual factor-grade HN filtrations. -/
noncomputable def tensorFiltrationSecondaryImage
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (q : E ⊗[K] F →ₗ[K] Q)
    {P : ℝ → Submodule K E} {R : ℝ → Submodule K F}
    (hP : Antitone P) (hR : Antitone R)
    {ι κ : Type*} (w : ι → ℝ) (z : κ → ℝ) (γ : ℝ) :
    ℝ → Submodule K (Submodule.FiltrationGraded
      (fun s ↦ (Submodule.tensorFiltration P R s).map q) γ) :=
  Submodule.imageFiltration
    (fun p : {ij : ι × κ // w ij.1 + z ij.2 = γ} ↦
      Submodule.tensorFiltrationGradedQuotientPair q hP hR p.property)
    (fun p ↦ Submodule.tensorFiltration
      ((V.filtrationGraded P (w p.val.1) hS).hermitianHNFiltration hS hN
        (hV.filtrationGraded P (w p.val.1)))
      ((W.filtrationGraded R (z p.val.2) hS).hermitianHNFiltration hS hN
        (hW.filtrationGraded R (z p.val.2))))

/-- Bost's global secondary weighted degree bound for the actual binary
quotient. The smaller-rank tensor-HN compatibility is explicit; canonical
pair contractions, finite spanning, the actual secondary images, and both
flag degree sums are proved. The eventual variation bound is separate. -/
theorem tensorFiltrationSecondaryImage_weighted_le_slope
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q)
    {P : ℝ → Submodule K E} {R : ℝ → Submodule K F}
    (hP : Antitone P) (hR : Antitone R)
    {ι κ : Type*} [Finite ι] [Finite κ]
    (b : Basis ι K E) (c : Basis κ K F) (w : ι → ℝ) (z : κ → ℝ)
    (hPw : ∀ t, P t = Submodule.span K (b '' {i | t ≤ w i}))
    (hRz : ∀ u, R u = Submodule.span K (c '' {j | u ≤ z j}))
    (hsmall : ∀ i j, finrank K (Submodule.FiltrationGraded P (w i)) +
      finrank K (Submodule.FiltrationGraded R (z j)) < finrank K E + finrank K F)
    (hInd : ∀ t u,
      finrank K (Submodule.FiltrationGraded P t) + finrank K (Submodule.FiltrationGraded R u) <
        finrank K E + finrank K F →
      (tensorFiltrationGradedSource V W hS hN hV hW P R t u).hermitianHNFiltration hS hN
        (tensorFiltrationGradedSource_isHermitian V W hS hN hV hW P R t u) =
      Submodule.tensorFiltration
        ((V.filtrationGraded P t hS).hermitianHNFiltration hS hN (hV.filtrationGraded P t))
        ((W.filtrationGraded R u hS).hermitianHNFiltration hS hN (hW.filtrationGraded R u))) :
    let T := V.orthogonalTensorPair W hS hN hV hW
    let B := T.pushforward q hq (T.isMeasurable.pushforward_of_discrete_or_countable hS q hq)
    (∑ᶠ γ : ℝ, ∑ᶠ t : ℝ, t * (finrank K (Submodule.FiltrationGraded
      (tensorFiltrationSecondaryImage V W hS hN hV hW q hP hR w z γ) t) : ℝ)) /
      (finrank K Q : ℝ) ≤ B.slope hS hN := by
  let T := V.orthogonalTensorPair W hS hN hV hW
  let B := T.pushforward q hq (T.isMeasurable.pushforward_of_discrete_or_countable hS q hq)
  let PQ : ℝ → Submodule K Q := fun s ↦ (Submodule.tensorFiltration P R s).map q
  let d : ℝ → ℝ := fun γ ↦ ∑ᶠ t : ℝ, t * (finrank K (Submodule.FiltrationGraded
    (tensorFiltrationSecondaryImage V W hS hN hV hW q hP hR w z γ) t) : ℝ)
  have hB : B.toNormFamily.IsHermitian hN :=
    (NormFamily.orthogonalTensorPair_isHermitian
      V.toNormFamily W.toNormFamily hN hV hW).pushforward q hq
  have hPQ : Antitone PQ := fun a b hab ↦ Submodule.map_mono
    (Submodule.antitone_tensorFiltration P R hab)
  obtain ⟨⟨a, ha⟩, ⟨b₀, hb₀⟩⟩ :=
    Submodule.tensorFiltration_attains_bot_top b c w z hPw hRz
  have hbot : ∃ s, PQ s = ⊥ := ⟨a, by simp [PQ, ha]⟩
  have htop : ∃ s, PQ s = ⊤ := ⟨b₀, by
    simp only [PQ, hb₀, Submodule.map_top, LinearMap.range_eq_top.mpr hq]⟩
  have hleft (t : ℝ) : ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → PQ s = PQ t := by
    obtain ⟨ε, hε, he⟩ := Submodule.tensorFiltration_locallyConstant_left b c w z hPw hRz t
    exact ⟨ε, hε, fun s hs hst ↦ congrArg (Submodule.map q) (he s hs hst)⟩
  have hz (γ : ℝ) (hγ : finrank K (Submodule.FiltrationGraded PQ γ) = 0) : d γ = 0 := by
    have := (Module.finrank_eq_zero_iff_of_free K (Submodule.FiltrationGraded PQ γ)).mp hγ
    have ht (t : ℝ) : finrank K (Submodule.FiltrationGraded
        (tensorFiltrationSecondaryImage V W hS hN hV hW q hP hR w z γ) t) = 0 :=
      Module.finrank_eq_zero_of_subsingleton K _
    simp only [d, ht, Nat.cast_zero, mul_zero, finsum_zero]
  have hd (γ : ℝ) : d γ ≤ (B.filtrationGraded PQ γ hS).degree hS hN :=
    tensorFiltrationQuotientGraded_secondary_degree_ge V W hS hN hV hW q hq hP hR
      b c w z hPw hRz γ (fun p ↦ hsmall p.val.1 p.val.2) hInd
  exact div_le_div_of_nonneg_right
    (finsum_le_degree_of_filtration_grade_bounds B hS hN hB PQ hPQ hbot htop hleft d hz hd)
    (Nat.cast_nonneg _)

end ArakelovGeometry.AdelicVectorBundle

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.ImageHN
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HN.OptimalVariation
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Tensor

/-!
# Degree bounds for binary graded tensor images

Binary tensors of grades map to the original quotient grade by the canonical
graded maps. Their completed contractions and spanning images give degree bounds
through the finite-image Harder–Narasimhan inequality.

The subquotient comparisons are restricted to binary real grades, within the
setting of [ChenMoriwaki2020], Remark 5.5.6. The variation result is an eventual
affine upper bound for the original quotient norm and chosen lifted
Harder–Narasimhan filtrations. Tensor compatibility of Harder–Narasimhan
filtrations in strictly smaller rank remains an explicit hypothesis.
The general variational inequality (5.13) is not proved here.
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

/-- The canonical graded pair map followed by the quotient-grade map.
The carrier and induced quotient norm are unchanged. -/
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

omit [FiniteDimensional K E] in
/-- Actual secondary cut membership gives the one-sided variation estimate
in the same source basis. Finite primary gaps control every nonzero matrix
coefficient; the determinant maximum is that of the actual quotient. -/
theorem eventual_image_expectation_le_of_graded_mem
    [FiniteDimensional K Q] {ι : Type*} [Finite ι]
    (b : Basis ι K E) (w s : ι → ℝ)
    (q : E →ₗ[K] Q) (hq : Function.Surjective q)
    {T L : ℝ → Submodule K Q}
    (d : Basis (Fin (finrank K Q)) K Q) (a r : Fin (finrank K Q) → ℝ)
    (hT : ∀ t, T t = span K (d '' {j | t ≤ a j}))
    (hL : ∀ t, L t = span K (d '' {j | t ≤ r j}))
    (hm : ∀ i, q (b i) ∈ T (w i))
    (hc : ∀ i, filtrationGradedMk T (w i) ⟨q (b i), hm i⟩ ∈
      filtrationOnGraded T L (w i) (s i)) :
    ∃ η > 0, ∀ ε, 0 < ε → ε < η →
      filtrationExpectation (fun t ↦ (weightedBasisVariation b w s ε t).map q) ≤
        filtrationExpectation T + ε * filtrationExpectation L := by
  classical
  have he : ∀ᶠ ε : ℝ in nhds 0, ∀ i j, w i < a j →
      w i + ε * s i ≤ a j + ε * r j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : w i < a j
    · have hf : ContinuousAt (fun ε : ℝ ↦ w i + ε * s i) 0 := by fun_prop
      have hg : ContinuousAt (fun ε : ℝ ↦ a j + ε * r j) 0 := by fun_prop
      filter_upwards [hf.eventually_lt hg (by simpa using hij)] with ε hε _
      exact hε.le
    · exact Filter.Eventually.of_forall fun _ h ↦ (hij h).elim
  obtain ⟨η, hη, he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨η, hη, fun ε hε hεη ↦ ?_⟩
  have hcoord (i : ι) : q (b i) ∈ span K (d ''
      {j | w i + ε * s i ≤ a j + ε * r j}) := by
    apply d.mem_span_image.mpr
    intro j hj
    have hn := Finsupp.mem_support_iff.mp hj
    rcases primary_lt_or_secondary_le_of_graded_mem d a r hT hL
      ⟨q (b i), hm i⟩ (hc i) j hn with hlt | hle
    · exact he (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using hεη) i j hlt
    · have hp : w i ≤ a j := d.mem_span_image.mp (hT (w i) ▸ hm i) hj
      exact add_le_add hp (mul_le_mul_of_nonneg_left hle hε.le)
  obtain ⟨σ, hσ, hmax, _⟩ := exists_quotient_expectation_maximum
    b (fun i ↦ w i + ε * s i) d q hq
  change filtrationExpectation (fun t ↦
    (span K (b '' {i | t ≤ w i + ε * s i})).map q) ≤ _
  rw [hmax, filtrationExpectation_eq_sum_weights d a hT,
    filtrationExpectation_eq_sum_weights d r hL]
  have hsum := sum_le_sum_weights_of_det_ne_zero d (fun j ↦ a j + ε * r j)
    (fun j ↦ w (σ j) + ε * s (σ j)) (fun j ↦ q (b (σ j)))
    (fun j ↦ hcoord (σ j)) ((mem_quotientDeterminantSupport b d q σ).mp hσ)
  have hh := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (finrank K Q))
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc] using hh

/-- Finite filtrations on every actual grade admit a simultaneous lifting.
The equality is on the original graded quotients, including zero grades. -/
theorem exists_lift_filtrationOnGraded
    (hP : Antitone P) (hbot : ∃ t, P t = ⊥) (htop : ∃ t, P t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P s = P t)
    (H : ∀ t, ℝ → Submodule K (FiltrationGraded P t))
    (hH : ∀ t, Antitone (H t)) (hHb : ∀ t, ∃ a, H t a = ⊥)
    (hHt : ∀ t, ∃ a, H t a = ⊤)
    (hHl : ∀ t a, ∃ ε > 0, ∀ s, a - ε < s → s ≤ a → H t s = H t a) :
    ∃ L : ℝ → Submodule K E, Antitone L ∧ (∃ t, L t = ⊥) ∧ (∃ t, L t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → L s = L t) ∧
      ∀ t, filtrationOnGraded P L t = H t := by
  classical
  obtain ⟨n, U, a, hU, hz, ht, _, _, _, hlevel, hright, hrec⟩ :=
    exists_strictMono_flag_and_jumps_of_antitone hP hbot htop hleft
  let D (A : Submodule K E × Submodule K E) :=
    {G : ℝ → Submodule K (A.1 ⧸ A.2.comap A.1.subtype) //
      Antitone G ∧ (∃ t, G t = ⊥) ∧ (∃ t, G t = ⊤) ∧
        ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → G s = G t}
  have hp (i : Fin n) : (P (a i), filtrationRightLimit P (a i)) =
      (U i.succ, U i.castSucc) := Prod.ext (hlevel i) (hright i)
  let d₀ (i : Fin n) : D (P (a i), filtrationRightLimit P (a i)) :=
    ⟨H (a i), hH (a i), hHb (a i), hHt (a i), hHl (a i)⟩
  let d₁ (i : Fin n) : D (U i.succ, U i.castSucc) := (hp i) ▸ d₀ i
  obtain ⟨_, _, _, _, L, _, _, _, _, hL, hLb, hLt, hLl, hc⟩ :=
    exists_lift_prescribed_filtrations U hU.monotone hz ht (fun i ↦ (d₁ i).val)
      (fun i ↦ (d₁ i).property.1) (fun i ↦ (d₁ i).property.2.1)
      (fun i ↦ (d₁ i).property.2.2.1) (fun i ↦ (d₁ i).property.2.2.2)
  refine ⟨L, hL, hLb, hLt, hLl, fun t ↦ ?_⟩
  by_cases hm : t ∈ Set.range a
  · obtain ⟨i, rfl⟩ := hm
    let PropCut (A : Submodule K E × Submodule K E) (d : D A) :=
      ∀ s, ((L s).comap A.1.subtype).map (A.2.comap A.1.subtype).mkQ = d.val s
    have transport {A B : Submodule K E × Submodule K E} (e : A = B) (d : D A) :
        PropCut B (e ▸ d) → PropCut A d := by
      cases e
      exact id
    exact funext (transport (hp i) (d₀ i) (hc i))
  · have := (Module.finrank_eq_zero_iff_of_free K (FiltrationGraded P t)).mp
      (finrank_filtrationGraded_eq_zero_of_flag U a hlevel hrec hm)
    exact Subsingleton.elim _ _

/-- Secondary weights on all actual primary grades sum to the weights of
any common adapted lifting basis. -/
theorem finsum_secondary_grades_eq_sum_weights
    {ι : Type*} [Fintype ι] (b : Basis ι K E) (w s : ι → ℝ)
    {L : ℝ → Submodule K E}
    (hP : ∀ t, P t = span K (b '' {i | t ≤ w i}))
    (hL : ∀ t, L t = span K (b '' {i | t ≤ s i})) :
    (∑ᶠ t : ℝ, ∑ᶠ a : ℝ, a *
      (finrank K (FiltrationGraded (filtrationOnGraded P L t) a) : ℝ)) = ∑ i, s i := by
  classical
  have hp : Antitone P := by
    rw [funext hP]
    exact antitone_span_weights b w
  have hl : Antitone L := by
    rw [funext hL]
    exact antitone_span_weights b s
  have hc (t a : ℝ) : finrank K (FiltrationGraded (filtrationOnGraded P L t) a) =
      (Finset.univ.filter fun i ↦ w i = t ∧ s i = a).card := by
    rw [finrank_filtrationGraded_filtrationOnGraded hp hl,
      filtrationJointMultiplicity_eq_card b w s hP hL]
  have hs (t : ℝ) : (∑ᶠ a : ℝ, a *
      (finrank K (FiltrationGraded (filtrationOnGraded P L t) a) : ℝ)) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ w i = t), s i := by
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image s) (by
      intro a ha
      by_contra hn
      have hz : (Finset.univ.filter fun i ↦ w i = t ∧ s i = a) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2.2⟩)
      exact ha (by simp only [hc, hz, Finset.card_empty, Nat.cast_zero, mul_zero]))]
    simp_rw [hc]
    have he := Finset.sum_fiberwise_of_maps_to'
      (s := Finset.univ.filter fun i ↦ w i = t) (t := Finset.univ.image s)
      (g := s) (fun i _ ↦ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      (fun a : ℝ ↦ a)
    simpa only [Finset.filter_filter, Finset.sum_const, nsmul_eq_mul, mul_comm] using he
  simp_rw [hs]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image w) (by
    intro t ht
    by_contra hn
    have hz : (Finset.univ.filter fun i ↦ w i = t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
    exact ht (by simp only [hz, Finset.sum_empty]))]
  exact Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image w)
    (g := w) (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩) s

end Submodule

namespace ArakelovGeometry.AdelicVectorBundle

universe u w wF w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} {F : Type wF} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  {Q : Type w'} [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- The chosen HN variation lift has the actual grade-HN cuts at every
real level. Its finite flag data also settle levels outside the jump set. -/
theorem HNVariationLift.filtrationOnGraded_eq
    [S.IsProper]
    {V : AdelicVectorBundle S}
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] {P : ℝ → Submodule K V}
    (L : V.HNVariationLift P) (t : ℝ) :
    Submodule.filtrationOnGraded P L.direction t =
      (V.filtrationGraded P t).hermitianHNFiltration (hV := (hV.filtrationGraded P t)) := by
  classical
  by_cases hm : t ∈ Set.range L.weight
  · obtain ⟨i, rfl⟩ := hm
    let C (A : Submodule K V × Submodule K V) :=
      ∀ s, ((L.direction s).comap A.1.subtype).map (A.2.comap A.1.subtype).mkQ =
        ((V.restrictOfNormMeasurability A.1).quotientOfNormMeasurability
          (A.2.comap A.1.subtype)).hermitianHNFiltration
          (hV := ((hV.restrict A.1).quotient (A.2.comap A.1.subtype))) s
    have hp : (P (L.weight i), Submodule.filtrationRightLimit P (L.weight i)) =
        (L.flag i.succ, L.flag i.castSucc) := Prod.ext (L.level i) (L.right i)
    have hc : C (L.flag i.succ, L.flag i.castSucc) := L.cuts i
    exact funext ((congrArg C hp).mpr hc)
  · have := (Module.finrank_eq_zero_iff_of_free K (Submodule.FiltrationGraded P t)).mp
      (Submodule.finrank_filtrationGraded_eq_zero_of_flag
        L.flag L.weight L.level L.reconstruct hm)
    exact Subsingleton.elim _ _

/-- The actual source bundle of a canonical binary graded pair. This is the
existing Hermitian tensor constructor applied to the actual two grades. -/
noncomputable abbrev tensorFiltrationGradedSource
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
    (P : ℝ → Submodule K V) (R : ℝ → Submodule K W) (t u : ℝ) :
    AdelicVectorBundle S :=
  (V.filtrationGraded P t).orthogonalTensorPair (W.filtrationGraded R u)
    (hV := (hV.filtrationGraded P t)) (hW := (hW.filtrationGraded R u))

instance tensorFiltrationGradedSource_isHermitian
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
    (P : ℝ → Submodule K V) (R : ℝ → Submodule K W) (t u : ℝ) :
    (tensorFiltrationGradedSource V W P R t u).toNormFamily.IsHermitian :=
  orthogonalTensorPair_isHermitian _ _

/-- The actual quotient of the original tensor bundle, followed by its
actual image-filtration grade. The target norm is not induced from a pair. -/
noncomputable abbrev tensorFiltrationQuotientGraded
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
    (q : V ⊗[K] W →ₗ[K] Q) (hq : Function.Surjective q)
    (P : ℝ → Submodule K V) (R : ℝ → Submodule K W) (γ : ℝ) :
    AdelicVectorBundle S :=
  let T := V.orthogonalTensorPair W
  (T.pushforward q hq
    (hm := (T.isMeasurable.pushforward_of_discrete_or_countable q hq))).filtrationGraded
    (fun s ↦ (Submodule.tensorFiltration P R s).map q) γ

instance tensorFiltrationQuotientGraded_isHermitian
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
    (q : V ⊗[K] W →ₗ[K] Q) (hq : Function.Surjective q)
    (P : ℝ → Submodule K V) (R : ℝ → Submodule K W) (γ : ℝ) :
    (tensorFiltrationQuotientGraded V W q hq P R γ).toNormFamily.IsHermitian := by
  dsimp only [tensorFiltrationQuotientGraded, filtrationGraded]
  apply NormFamily.IsHermitian.quotient
  apply NormFamily.IsHermitian.restrict
  exact (NormFamily.orthogonalTensorPair_isHermitian
    V.toNormFamily W.toNormFamily).pushforward q hq

variable [S.IsProper]

/-- The canonical binary pair family satisfies the finite-image
Harder–Narasimhan degree bound in each quotient grade. Spanning and contraction
follow from surjectivity of the graded quotient map and the completed pair
contraction. -/
theorem tensorFiltrationQuotientGraded_hnImage_degree_ge
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
    (q : V ⊗[K] W →ₗ[K] Q) (hq : Function.Surjective q)
    {P : ℝ → Submodule K V} {R : ℝ → Submodule K W}
    (hP : Antitone P) (hR : Antitone R)
    {ι κ : Type*} [Finite ι] [Finite κ]
    (b : Basis ι K V) (c : Basis κ K W) (w : ι → ℝ) (z : κ → ℝ)
    (hPw : ∀ t, P t = Submodule.span K (b '' {i | t ≤ w i}))
    (hRz : ∀ u, R u = Submodule.span K (c '' {j | u ≤ z j})) (γ : ℝ) :
    let J := {ij : ι × κ // w ij.1 + z ij.2 = γ}
    let C := fun p : J ↦ tensorFiltrationGradedSource V W P R (w p.val.1) (z p.val.2)
    let hC := fun p : J ↦ tensorFiltrationGradedSource_isHermitian V W P R
      (w p.val.1) (z p.val.2)
    let g := fun p : J ↦ Submodule.tensorFiltrationGradedQuotientPair q hP hR p.property
    let H := Submodule.imageFiltration g (fun p ↦ (C p).hermitianHNFiltration (hV := (hC p)))
    (∑ᶠ t : ℝ, t * (finrank K (Submodule.FiltrationGraded H t) : ℝ)) ≤
      (tensorFiltrationQuotientGraded V W q hq P R γ).degree := by
  dsimp only
  apply finsum_hermitianHN_imageFiltration_le_degree
    (fun p : {ij : ι × κ // w ij.1 + z ij.2 = γ} ↦
      tensorFiltrationGradedSource V W P R (w p.val.1) (z p.val.2))
    (tensorFiltrationQuotientGraded V W q hq P R γ)
    (fun p ↦ Submodule.tensorFiltrationGradedQuotientPair q hP hR p.property)
    (Submodule.iSup_range_tensorFiltrationGradedQuotientPair b c w z q hP hR hPw hRz γ)
  intro p ω x
  exact NormFamily.tensorFiltrationGradedPair_pushforward_norm_le V.toNormFamily W.toNormFamily
    q hq hP hR p.property ω x

/-- Under tensor compatibility of Harder–Narasimhan filtrations in
strictly smaller rank, the canonical pair images of the secondary tensor
filtrations satisfy the weighted degree bound on each quotient grade. -/
theorem tensorFiltrationQuotientGraded_secondary_degree_ge
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
    (q : V ⊗[K] W →ₗ[K] Q) (hq : Function.Surjective q)
    {P : ℝ → Submodule K V} {R : ℝ → Submodule K W}
    (hP : Antitone P) (hR : Antitone R)
    {ι κ : Type*} [Finite ι] [Finite κ]
    (b : Basis ι K V) (c : Basis κ K W) (w : ι → ℝ) (z : κ → ℝ)
    (hPw : ∀ t, P t = Submodule.span K (b '' {i | t ≤ w i}))
    (hRz : ∀ u, R u = Submodule.span K (c '' {j | u ≤ z j})) (γ : ℝ)
    (hsmall : ∀ p : {ij : ι × κ // w ij.1 + z ij.2 = γ},
      finrank K (Submodule.FiltrationGraded P (w p.val.1)) +
        finrank K (Submodule.FiltrationGraded R (z p.val.2)) < finrank K V + finrank K W)
    (hInd : ∀ t u,
      finrank K (Submodule.FiltrationGraded P t) + finrank K (Submodule.FiltrationGraded R u) <
        finrank K V + finrank K W →
      (tensorFiltrationGradedSource V W P R t u).hermitianHNFiltration
        (hV := (tensorFiltrationGradedSource_isHermitian V W P R t u)) =
      Submodule.tensorFiltration
        ((V.filtrationGraded P t).hermitianHNFiltration (hV := (hV.filtrationGraded P t)))
        ((W.filtrationGraded R u).hermitianHNFiltration (hV := (hW.filtrationGraded R u)))) :
    let J := {ij : ι × κ // w ij.1 + z ij.2 = γ}
    let g := fun p : J ↦ Submodule.tensorFiltrationGradedQuotientPair q hP hR p.property
    let H := Submodule.imageFiltration g (fun p ↦ Submodule.tensorFiltration
      ((V.filtrationGraded P (w p.val.1)).hermitianHNFiltration
        (hV := (hV.filtrationGraded P (w p.val.1))))
      ((W.filtrationGraded R (z p.val.2)).hermitianHNFiltration
        (hV := (hW.filtrationGraded R (z p.val.2)))))
    (∑ᶠ t : ℝ, t * (finrank K (Submodule.FiltrationGraded H t) : ℝ)) ≤
      (tensorFiltrationQuotientGraded V W q hq P R γ).degree := by
  have h := tensorFiltrationQuotientGraded_hnImage_degree_ge V W q hq
    hP hR b c w z hPw hRz γ
  have he : (fun p : {ij : ι × κ // w ij.1 + z ij.2 = γ} ↦
      (tensorFiltrationGradedSource V W P R
        (w p.val.1) (z p.val.2)).hermitianHNFiltration
          (hV := (tensorFiltrationGradedSource_isHermitian V W P R
          (w p.val.1) (z p.val.2)))) =
      (fun p : {ij : ι × κ // w ij.1 + z ij.2 = γ} ↦ Submodule.tensorFiltration
        ((V.filtrationGraded P (w p.val.1)).hermitianHNFiltration
          (hV := (hV.filtrationGraded P (w p.val.1))))
        ((W.filtrationGraded R (z p.val.2)).hermitianHNFiltration
          (hV := (hW.filtrationGraded R (z p.val.2))))) :=
    funext fun p ↦ hInd _ _ (hsmall p)
  dsimp only at h ⊢
  rw [he] at h
  exact h

/-- The actual secondary image in a primary quotient grade, formed from the
tensor products of the actual factor-grade HN filtrations. -/
noncomputable def tensorFiltrationSecondaryImage
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
    (q : V ⊗[K] W →ₗ[K] Q)
    {P : ℝ → Submodule K V} {R : ℝ → Submodule K W}
    (hP : Antitone P) (hR : Antitone R)
    {ι κ : Type*} (w : ι → ℝ) (z : κ → ℝ) (γ : ℝ) :
    ℝ → Submodule K (Submodule.FiltrationGraded
      (fun s ↦ (Submodule.tensorFiltration P R s).map q) γ) :=
  Submodule.imageFiltration
    (fun p : {ij : ι × κ // w ij.1 + z ij.2 = γ} ↦
      Submodule.tensorFiltrationGradedQuotientPair q hP hR p.property)
    (fun p ↦ Submodule.tensorFiltration
      ((V.filtrationGraded P (w p.val.1)).hermitianHNFiltration
        (hV := (hV.filtrationGraded P (w p.val.1))))
      ((W.filtrationGraded R (z p.val.2)).hermitianHNFiltration
        (hV := (hW.filtrationGraded R (z p.val.2)))))

/-- The sum of the secondary grade weights, divided by the quotient rank,
is at most the slope of the binary quotient. Tensor compatibility of Harder–Narasimhan
filtrations in strictly smaller rank is an explicit hypothesis. -/
theorem tensorFiltrationSecondaryImage_weighted_le_slope
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
    (q : V ⊗[K] W →ₗ[K] Q) (hq : Function.Surjective q)
    {P : ℝ → Submodule K V} {R : ℝ → Submodule K W}
    (hP : Antitone P) (hR : Antitone R)
    {ι κ : Type*} [Finite ι] [Finite κ]
    (b : Basis ι K V) (c : Basis κ K W) (w : ι → ℝ) (z : κ → ℝ)
    (hPw : ∀ t, P t = Submodule.span K (b '' {i | t ≤ w i}))
    (hRz : ∀ u, R u = Submodule.span K (c '' {j | u ≤ z j}))
    (hsmall : ∀ i j, finrank K (Submodule.FiltrationGraded P (w i)) +
      finrank K (Submodule.FiltrationGraded R (z j)) < finrank K V + finrank K W)
    (hInd : ∀ t u,
      finrank K (Submodule.FiltrationGraded P t) + finrank K (Submodule.FiltrationGraded R u) <
        finrank K V + finrank K W →
      (tensorFiltrationGradedSource V W P R t u).hermitianHNFiltration
        (hV := (tensorFiltrationGradedSource_isHermitian V W P R t u)) =
      Submodule.tensorFiltration
        ((V.filtrationGraded P t).hermitianHNFiltration (hV := (hV.filtrationGraded P t)))
        ((W.filtrationGraded R u).hermitianHNFiltration (hV := (hW.filtrationGraded R u)))) :
    let T := V.orthogonalTensorPair W
    let B := T.pushforward q hq (hm := (T.isMeasurable.pushforward_of_discrete_or_countable q hq))
    (∑ᶠ γ : ℝ, ∑ᶠ t : ℝ, t * (finrank K (Submodule.FiltrationGraded
      (tensorFiltrationSecondaryImage V W q hP hR w z γ) t) : ℝ)) /
      (finrank K Q : ℝ) ≤ B.slope := by
  let T := V.orthogonalTensorPair W
  let B := T.pushforward q hq (hm := (T.isMeasurable.pushforward_of_discrete_or_countable q hq))
  let PQ : ℝ → Submodule K Q := fun s ↦ (Submodule.tensorFiltration P R s).map q
  let d : ℝ → ℝ := fun γ ↦ ∑ᶠ t : ℝ, t * (finrank K (Submodule.FiltrationGraded
    (tensorFiltrationSecondaryImage V W q hP hR w z γ) t) : ℝ)
  have hB : B.toNormFamily.IsHermitian :=
    (NormFamily.orthogonalTensorPair_isHermitian
      V.toNormFamily W.toNormFamily).pushforward q hq
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
        (tensorFiltrationSecondaryImage V W q hP hR w z γ) t) = 0 :=
      Module.finrank_eq_zero_of_subsingleton K _
    simp only [d, ht, Nat.cast_zero, mul_zero, finsum_zero]
  have hd (γ : ℝ) : d γ ≤ (B.filtrationGraded PQ γ).degree :=
    tensorFiltrationQuotientGraded_secondary_degree_ge V W q hq hP hR
      b c w z hPw hRz γ (fun p ↦ hsmall p.val.1 p.val.2) hInd
  exact div_le_div_of_nonneg_right
    (finsum_le_degree_of_filtration_grade_bounds B (hW := hB) PQ hPQ hbot htop hleft d hz hd)
    (Nat.cast_nonneg _)

/-- The normalized secondary image weight is at most the original quotient slope
and is the linear coefficient of an eventual affine upper bound on the quotient expectation.
The comparison uses the chosen lifted Harder–Narasimhan filtrations and common
bases. Tensor compatibility in strictly smaller rank is assumed. This is a
one-sided binary estimate, without the general inequality (5.13) of
[ChenMoriwaki2020]. -/
theorem tensorFiltrationQuotient_eventual_hn_upper
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.toNormFamily.IsHermitian] [hW : W.toNormFamily.IsHermitian]
    (q : V ⊗[K] W →ₗ[K] Q) (hq : Function.Surjective q)
    {P : ℝ → Submodule K V} {R : ℝ → Submodule K W}
    (hP : Antitone P) (hR : Antitone R)
    {ι κ : Type*} [Finite ι] [Finite κ]
    (b : Basis ι K V) (c : Basis κ K W) (w : ι → ℝ) (z : κ → ℝ)
    (hPw : ∀ t, P t = Submodule.span K (b '' {i | t ≤ w i}))
    (hRz : ∀ u, R u = Submodule.span K (c '' {j | u ≤ z j}))
    (L : V.HNVariationLift P) (M : W.HNVariationLift R)
    (s : ι → ℝ) (v : κ → ℝ)
    (hLs : ∀ t, L.direction t = Submodule.span K (b '' {i | t ≤ s i}))
    (hMv : ∀ t, M.direction t = Submodule.span K (c '' {j | t ≤ v j}))
    (hsmall : ∀ i j, finrank K (Submodule.FiltrationGraded P (w i)) +
      finrank K (Submodule.FiltrationGraded R (z j)) < finrank K V + finrank K W)
    (hInd : ∀ t u,
      finrank K (Submodule.FiltrationGraded P t) + finrank K (Submodule.FiltrationGraded R u) <
        finrank K V + finrank K W →
      (tensorFiltrationGradedSource V W P R t u).hermitianHNFiltration
        (hV := (tensorFiltrationGradedSource_isHermitian V W P R t u)) =
      Submodule.tensorFiltration
        ((V.filtrationGraded P t).hermitianHNFiltration (hV := (hV.filtrationGraded P t)))
        ((W.filtrationGraded R u).hermitianHNFiltration (hV := (hW.filtrationGraded R u)))) :
    let T := V.orthogonalTensorPair W
    let B := T.pushforward q hq (hm := (T.isMeasurable.pushforward_of_discrete_or_countable q hq))
    let δ := (∑ᶠ γ : ℝ, ∑ᶠ t : ℝ, t * (finrank K (Submodule.FiltrationGraded
      (tensorFiltrationSecondaryImage V W q hP hR w z γ) t) : ℝ)) /
      (finrank K Q : ℝ)
    δ ≤ B.slope ∧ ∃ η > 0, ∀ ε, 0 < ε → ε < η →
      Submodule.filtrationExpectation (fun t ↦
        (Submodule.tensorFiltration (Submodule.weightedBasisVariation b w s ε)
          (Submodule.weightedBasisVariation c z v ε) t).map q) ≤
      Submodule.filtrationExpectation (fun t ↦ (Submodule.tensorFiltration P R t).map q) +
        ε * δ := by
  classical
  dsimp only
  refine ⟨tensorFiltrationSecondaryImage_weighted_le_slope V W q hq
    hP hR b c w z hPw hRz hsmall hInd, ?_⟩
  let PQ : ℝ → Submodule K Q := fun t ↦ (Submodule.tensorFiltration P R t).map q
  let H := tensorFiltrationSecondaryImage V W q hP hR w z
  have hfinite (γ : ℝ) : Antitone (H γ) ∧ (∃ t, H γ t = ⊥) ∧ (∃ t, H γ t = ⊤) ∧
      ∀ t, ∃ ε > 0, ∀ a, t - ε < a → a ≤ t → H γ a = H γ t := by
    let J := {ij : ι × κ // w ij.1 + z ij.2 = γ}
    let C := fun p : J ↦ tensorFiltrationGradedSource V W P R
      (w p.val.1) (z p.val.2)
    let hC := fun p : J ↦ tensorFiltrationGradedSource_isHermitian V W P R
      (w p.val.1) (z p.val.2)
    let g := fun p : J ↦ Submodule.tensorFiltrationGradedQuotientPair q hP hR p.property
    have he : H γ = Submodule.imageFiltration g
        (fun p ↦ (C p).hermitianHNFiltration (hV := (hC p))) := by
      apply congrArg (Submodule.imageFiltration g)
      funext p
      exact (hInd _ _ (hsmall p.val.1 p.val.2)).symm
    rw [he]
    exact hermitianHN_imageFiltration_finite C g (hV := hC)
      (Submodule.iSup_range_tensorFiltrationGradedQuotientPair b c w z q hP hR hPw hRz γ)
  obtain ⟨d₀, a₀, hd₀⟩ := Submodule.exists_weighted_basis_image
    (b.tensorProduct c) (fun p ↦ w p.1 + z p.2) q hq
  have hPQ (t : ℝ) : PQ t = Submodule.span K (d₀ '' {i | t ≤ a₀ i}) := by
    dsimp only [PQ]
    rw [Submodule.tensorFiltration_eq_span_tensorProduct b c w z hPw hRz]
    exact hd₀ t
  have hPQa : Antitone PQ := by
    rw [funext hPQ]
    exact Submodule.antitone_span_weights d₀ a₀
  obtain ⟨hPQb, hPQt⟩ := Submodule.span_weights_attains_bot_top d₀ a₀
  have hPQl := Submodule.span_weights_locallyConstant_left d₀ a₀
  simp_rw [← hPQ] at hPQb hPQt hPQl
  obtain ⟨N, hNant, hNb, hNt, hNl, hcuts⟩ := Submodule.exists_lift_filtrationOnGraded
    hPQa hPQb hPQt hPQl H (fun γ ↦ (hfinite γ).1)
    (fun γ ↦ (hfinite γ).2.1) (fun γ ↦ (hfinite γ).2.2.1)
    (fun γ ↦ (hfinite γ).2.2.2)
  obtain ⟨d, a, r, hd, hNr, _, _⟩ := Submodule.exists_common_weighted_basis
    hPQa hPQb hPQt hPQl hNant hNb hNt hNl
  have hmean : Submodule.filtrationExpectation N =
      (∑ᶠ γ : ℝ, ∑ᶠ t : ℝ, t * (finrank K (Submodule.FiltrationGraded (H γ) t) : ℝ)) /
        (finrank K Q : ℝ) := by
    rw [Submodule.filtrationExpectation_eq_sum_weights d r hNr]
    congr 1
    have hh := Submodule.finsum_secondary_grades_eq_sum_weights d a r hd hNr
    have heq : Submodule.filtrationOnGraded PQ N = H := funext hcuts
    rw [heq] at hh
    exact hh.symm
  have hb (i : ι) : b i ∈ P (w i) := by
    rw [hPw]
    exact Submodule.subset_span ⟨i, (show w i ≤ w i from le_rfl), rfl⟩
  have hc (j : κ) : c j ∈ R (z j) := by
    rw [hRz]
    exact Submodule.subset_span ⟨j, (show z j ≤ z j from le_rfl), rfl⟩
  have hH (t u : ℝ) :
      (V.filtrationGraded P t).hermitianHNFiltration (hV := (hV.filtrationGraded P t)) u =
        Submodule.span K (Submodule.filtrationGradedGenerator b w hb t ''
          {i | u ≤ s i.val}) := by
    rw [← L.filtrationOnGraded_eq]
    exact Submodule.filtrationOnGraded_eq_span_generators b w s hPw hLs hb t u
  have hJ (t u : ℝ) :
      (W.filtrationGraded R t).hermitianHNFiltration (hV := (hW.filtrationGraded R t)) u =
        Submodule.span K (Submodule.filtrationGradedGenerator c z hc t ''
          {i | u ≤ v i.val}) := by
    rw [← M.filtrationOnGraded_eq]
    exact Submodule.filtrationOnGraded_eq_span_generators c z v hRz hMv hc t u
  have hspan (γ ℓ : ℝ) : H γ ℓ = Submodule.span K
      (Submodule.tensorQuotientGradedGenerator b c w z hb hc q hP hR γ ''
        {p | ℓ ≤ s p.val.1 + v p.val.2}) :=
    Submodule.imageFiltration_tensor_secondary_eq_span b c w z hb hc q hP hR s v _ _ hH hJ γ ℓ
  have hm (p : ι × κ) : q ((b.tensorProduct c) p) ∈ PQ (w p.1 + z p.2) := by
    dsimp only [PQ]
    rw [Submodule.tensorFiltration_eq_span_tensorProduct b c w z hPw hRz]
    exact ⟨(b.tensorProduct c) p, Submodule.subset_span
      ⟨p, (show w p.1 + z p.2 ≤ w p.1 + z p.2 from le_rfl), rfl⟩, rfl⟩
  have hclass (p : ι × κ) : Submodule.filtrationGradedMk PQ (w p.1 + z p.2)
      ⟨q ((b.tensorProduct c) p), hm p⟩ ∈
        Submodule.filtrationOnGraded PQ N (w p.1 + z p.2) (s p.1 + v p.2) := by
    rw [hcuts, hspan]
    refine Submodule.subset_span
      ⟨⟨p, rfl⟩, (show s p.1 + v p.2 ≤ s p.1 + v p.2 from le_rfl), ?_⟩
    dsimp only [Submodule.tensorQuotientGradedGenerator,
      Submodule.tensorFiltrationGradedQuotientPair, Submodule.filtrationGradedGenerator,
      LinearMap.comp_apply]
    rw [Submodule.tensorFiltrationGradedPair_mk, Submodule.filtrationGradedMap_mk]
    congr 1
    apply Subtype.ext
    exact congrArg q (Basis.tensorProduct_apply b c p.1 p.2).symm
  obtain ⟨η, hη, hu⟩ := Submodule.eventual_image_expectation_le_of_graded_mem
    (b.tensorProduct c) (fun p ↦ w p.1 + z p.2) (fun p ↦ s p.1 + v p.2)
    q hq d a r hd hNr hm hclass
  refine ⟨η, hη, fun ε hε he ↦ ?_⟩
  have hvar : Submodule.tensorFiltration (Submodule.weightedBasisVariation b w s ε)
      (Submodule.weightedBasisVariation c z v ε) =
      Submodule.weightedBasisVariation (b.tensorProduct c)
        (fun p ↦ w p.1 + z p.2) (fun p ↦ s p.1 + v p.2) ε := by
    funext t
    unfold Submodule.weightedBasisVariation
    rw [Submodule.tensorFiltration_eq_span_tensorProduct b c
      (fun i ↦ w i + ε * s i) (fun j ↦ z j + ε * v j) (fun _ ↦ rfl) (fun _ ↦ rfl)]
    congr 2
    ext p
    change (t ≤ (w p.1 + ε * s p.1) + (z p.2 + ε * v p.2)) ↔
      t ≤ (w p.1 + z p.2) + ε * (s p.1 + v p.2)
    ring_nf
  rw [hvar]
  simpa only [hmean] using hu ε hε he

end ArakelovGeometry.AdelicVectorBundle

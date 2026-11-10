/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.LogarithmicMinimaRestriction

/-!
# Intrinsic ordinary minima of actual completed norm families

Degrees, threshold spans, minima and the completed filtration use the literal
rational norm evaluations. Domination and primal measurability suffice for their
integrable vector degrees. The completed restriction has those properties without
requiring dual measurability or a measurable-base restriction constructor.
-/

@[expose] public section

namespace ArakelovGeometry.NormFamily


noncomputable section
universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The span of actual nonzero rational vectors of degree at least the threshold. -/
def degreeThresholdSpan (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (t : ℝ)
    : Submodule K E :=
  Submodule.span K {x | ∃ hx : x ≠ 0, t ≤ (ξ.vectorDegree hd hm) ⟨x, hx⟩}

/-- Ordinary logarithmic minima. Source indices are `1 ≤ i ≤ finrank K E`;
index zero and indices above rank give the explicit extended endpoint conventions. -/
def logarithmicMinimum (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (i : ℕ) :
    EReal :=
  ⨆ (t : ℝ) (_ : i ≤ Module.finrank K ((ξ.degreeThresholdSpan hd hm) t)), (t : EReal)

/-- The first ordinary logarithmic minimum, equal to `⊥` in rank zero. -/
def maximalLogarithmicMinimum (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) :
    EReal :=
  (ξ.logarithmicMinimum hd hm) 1

/-- The last ordinary logarithmic minimum, equal to `⊤` in rank zero. -/
def minimalLogarithmicMinimum (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) :
    EReal :=
  (ξ.logarithmicMinimum hd hm) (Module.finrank K E)

/-- The source's completed decreasing minima filtration. -/
def minimaFiltration (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (t : ℝ) :
    Submodule K E :=
  ⨅ (ε : ℝ) (_ : 0 < ε), (ξ.degreeThresholdSpan hd hm) (t - ε)

/-- Every actual high-degree generator belongs to its threshold span. -/
theorem mem_degreeThresholdSpan (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable)
    (s : {x : E // x ≠ 0})
    {t : ℝ} (hs : t ≤ (ξ.vectorDegree hd hm) s) : s.val ∈ (ξ.degreeThresholdSpan hd hm) t :=
  Submodule.subset_span ⟨s.property, hs⟩

/-- Increasing a degree threshold decreases the actual generated subspace. -/
theorem degreeThresholdSpan_antitone (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable) :
    Antitone (ξ.degreeThresholdSpan hd hm) := by
  intro a b hab
  apply Submodule.span_mono
  rintro x ⟨hx, hxb⟩
  exact ⟨hx, hab.trans hxb⟩

/-- Every admissible real threshold is bounded by its extended minimum. -/
theorem coe_le_logarithmicMinimum_of_finrank_le (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable)
    {i : ℕ} {t : ℝ} (ht : i ≤ Module.finrank K ((ξ.degreeThresholdSpan hd hm) t)) :
    (t : EReal) ≤ (ξ.logarithmicMinimum hd hm) i :=
  le_iSup_of_le t (le_iSup_of_le ht le_rfl)

/-- Ordinary logarithmic minima are nonincreasing with their natural index. -/
theorem logarithmicMinimum_antitone (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable) :
    Antitone (ξ.logarithmicMinimum hd hm) := by
  intro i j hij
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact (ξ.coe_le_logarithmicMinimum_of_finrank_le hd hm) (hij.trans ht)

/-- Index zero admits every real threshold; its extended minimum is `⊤`. -/
theorem logarithmicMinimum_zero (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) :
    (ξ.logarithmicMinimum hd hm) 0 = ⊤ := by
  apply top_unique
  apply EReal.ge_of_forall_gt_iff_ge.mp
  intro t _
  exact (ξ.coe_le_logarithmicMinimum_of_finrank_le hd hm) (Nat.zero_le _)

/-- Indices above the actual rank have no admissible thresholds. -/
theorem logarithmicMinimum_eq_bot_of_finrank_lt (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable)
    {i : ℕ} (hi : Module.finrank K E < i) : (ξ.logarithmicMinimum hd hm) i = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact False.elim ((not_le_of_gt ((Submodule.finrank_le _).trans_lt hi)) ht)

/-- Every threshold span is contained in the source's completed minima filtration. -/
theorem degreeThresholdSpan_le_minimaFiltration (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable) (t : ℝ) :
    (ξ.degreeThresholdSpan hd hm) t ≤ (ξ.minimaFiltration hd hm) t := by
  apply le_iInf
  intro ε
  apply le_iInf
  intro hε
  exact (ξ.degreeThresholdSpan_antitone hd hm) (sub_le_self _ hε.le)

/-- The completed filtration is contained in every strictly relaxed threshold span. -/
theorem minimaFiltration_le_degreeThresholdSpan (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) : (ξ.minimaFiltration hd hm) t ≤ (ξ.degreeThresholdSpan hd hm) (t - ε) :=
  iInf_le_of_le ε (iInf_le_of_le hε le_rfl)

/-- An actual high-degree nonzero vector belongs to the completed minima filtration. -/
theorem mem_minimaFiltration_of_degree_ge (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable)
    (s : {x : E // x ≠ 0}) {t : ℝ} (hs : t ≤ (ξ.vectorDegree hd hm) s) :
    s.val ∈ (ξ.minimaFiltration hd hm) t :=
  (ξ.degreeThresholdSpan_le_minimaFiltration hd hm) t ((ξ.mem_degreeThresholdSpan hd hm) s hs)

/-- The whole rational line of an actual high-degree vector lies in the minima filtration. -/
theorem span_singleton_le_minimaFiltration (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable)
    (s : {x : E // x ≠ 0}) {t : ℝ} (hs : t ≤ (ξ.vectorDegree hd hm) s) :
    Submodule.span K {s.val} ≤ (ξ.minimaFiltration hd hm) t :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr ((ξ.mem_minimaFiltration_of_degree_ge hd hm) s hs)

/-- The source minima filtration decreases with its real parameter. -/
theorem minimaFiltration_antitone (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) :
    Antitone (ξ.minimaFiltration hd hm) := by
  intro a b hab
  apply le_iInf
  intro ε
  apply le_iInf
  intro hε
  exact ((ξ.minimaFiltration_le_degreeThresholdSpan hd hm) b hε).trans
    ((ξ.degreeThresholdSpan_antitone hd hm) (sub_le_sub_right hab ε))

/-- The completed minima filtration is left continuous, without a finiteness premise. -/
theorem minimaFiltration_eq_iInf_lt (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable) (t : ℝ) :
    (ξ.minimaFiltration hd hm) t = ⨅ (u : ℝ) (_ : u < t), (ξ.minimaFiltration hd hm) u := by
  apply le_antisymm
  · exact le_iInf (fun u => le_iInf (fun hu => (ξ.minimaFiltration_antitone hd hm) hu.le))
  · apply le_iInf
    intro ε
    apply le_iInf
    intro hε
    have hhalf : 0 < ε / 2 := half_pos hε
    have hu : t - ε / 2 < t := sub_lt_self _ hhalf
    have hstep : (⨅ (u : ℝ) (_ : u < t), (ξ.minimaFiltration hd hm) u) ≤
        (ξ.minimaFiltration hd hm) (t - ε / 2) :=
      iInf_le_of_le (t - ε / 2) (iInf_le_of_le hu le_rfl)
    have h := hstep.trans
      ((ξ.minimaFiltration_le_degreeThresholdSpan hd hm) (t - ε / 2) hhalf)
    convert h using 1
    congr 1
    ring

/-- A rank-zero bundle has no nonzero threshold generators. -/
theorem degreeThresholdSpan_eq_bot_of_finrank_eq_zero (ξ : NormFamily S E) (hd : ξ.IsDominated)
    (hm : ξ.IsMeasurable)
    (hr : Module.finrank K E = 0) (t : ℝ) : (ξ.degreeThresholdSpan hd hm) t = ⊥ := by
  have hz : ∀ x : E, x = 0 := finrank_zero_iff_forall_zero.mp hr
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨hx, _⟩
  exact False.elim (hx (hz x))

/-- Every ordinary minima filtration space is zero in rank zero. -/
theorem minimaFiltration_eq_bot_of_finrank_eq_zero (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm
    : ξ.IsMeasurable)
    (hr : Module.finrank K E = 0) (t : ℝ) : (ξ.minimaFiltration hd hm) t = ⊥ := by
  apply le_antisymm _ bot_le
  exact ((ξ.minimaFiltration_le_degreeThresholdSpan hd hm) t (by norm_num : (0 : ℝ) < 1)).trans
    ((ξ.degreeThresholdSpan_eq_bot_of_finrank_eq_zero hd hm) hr (t - 1)).le

/-- The first minimum has the source rank-zero convention `-∞`. -/
theorem maximalLogarithmicMinimum_eq_bot_of_finrank_eq_zero (ξ : NormFamily S E) (hd :
    ξ.IsDominated) (hm : ξ.IsMeasurable)
    (hr : Module.finrank K E = 0) : (ξ.maximalLogarithmicMinimum hd hm) = ⊥ :=
  (ξ.logarithmicMinimum_eq_bot_of_finrank_lt hd hm) (by rw [hr]; exact Nat.zero_lt_one)

/-- The last minimum has the source rank-zero convention `+∞`. -/
theorem minimalLogarithmicMinimum_eq_top_of_finrank_eq_zero (ξ : NormFamily S E) (hd :
    ξ.IsDominated) (hm : ξ.IsMeasurable)
    (hr : Module.finrank K E = 0) : (ξ.minimalLogarithmicMinimum hd hm) = ⊤ := by
  rw [minimalLogarithmicMinimum, hr, (ξ.logarithmicMinimum_zero hd hm)]

/-- Source Definition 4.3.69's attained-threshold characterization. The source
indices are positive and at most rank; `i = 0` also allows the empty family. -/
theorem le_finrank_degreeThresholdSpan_iff (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable)
    (i : ℕ) (t : ℝ) :
    i ≤ Module.finrank K ((ξ.degreeThresholdSpan hd hm) t) ↔
      ∃ s : Fin i → {x : E // x ≠ 0},
        LinearIndependent K (fun j => (s j).val) ∧
        ∀ j, t ≤ (ξ.vectorDegree hd hm) (s j) := by
  classical
  constructor
  · intro hi
    obtain ⟨f, hf, _, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq K
      {x : E | ∃ hx : x ≠ 0, t ≤ (ξ.vectorDegree hd hm) ⟨x, hx⟩}
    choose hn hd using fun j : Fin i => hf (Fin.castLE hi j)
    refine ⟨fun j => ⟨f (Fin.castLE hi j), hn j⟩, ?_, hd⟩
    exact hli.comp (Fin.castLE hi) (Fin.castLE_injective hi)
  · rintro ⟨s, hli, hs⟩
    have hspan : Submodule.span K (Set.range fun j => (s j).val) ≤
        (ξ.degreeThresholdSpan hd hm) t := by
      apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      exact (ξ.mem_degreeThresholdSpan hd hm) (s j) (hs j)
    have hcard : Module.finrank K (Submodule.span K (Set.range fun j => (s j).val)) = i := by
      simpa using finrank_span_eq_card hli
    rw [← hcard]
    exact Submodule.finrank_mono hspan


/-- Each actual left-completed cut is an actual relaxed threshold span.
This is subspace stabilization, not attainment of degrees at the cut itself. -/
theorem exists_minimaFiltration_eq_degreeThresholdSpan (ξ : NormFamily S E) (hd : ξ.IsDominated)
    (hm : ξ.IsMeasurable)
    (t : ℝ) : ∃ ε : ℝ, 0 < ε ∧ (ξ.minimaFiltration hd hm) t = (ξ.degreeThresholdSpan hd hm) (t -
        ε) := by
  classical
  let : Nonempty {ε : ℝ // 0 < ε} := ⟨⟨1, zero_lt_one⟩⟩
  let f : {ε : ℝ // 0 < ε} → ℕ := fun ε =>
    Module.finrank K ((ξ.degreeThresholdSpan hd hm) (t - ε.val))
  let ε₀ := Function.argmin f
  refine ⟨ε₀.val, ε₀.property,
    le_antisymm ((ξ.minimaFiltration_le_degreeThresholdSpan hd hm) t ε₀.property) ?_⟩
  apply le_iInf
  intro ε
  apply le_iInf
  intro hε
  rcases le_total ε₀.val ε with hle | hle
  · exact (ξ.degreeThresholdSpan_antitone hd hm) (sub_le_sub_left hle t)
  · have hspan := (ξ.degreeThresholdSpan_antitone hd hm) (sub_le_sub_left hle t)
    have hr : Module.finrank K ((ξ.degreeThresholdSpan hd hm) (t - ε₀.val)) ≤
        Module.finrank K ((ξ.degreeThresholdSpan hd hm) (t - ε)) :=
      Function.argmin_le f ⟨ε, hε⟩
    exact (Submodule.eq_of_le_of_finrank_le hspan hr).symm.le

/-- Actual completed filtration rank is characterized by the extended supremum
minimum. The natural-index endpoint extensions are also covered. -/
theorem le_finrank_minimaFiltration_iff (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable) (i : ℕ) (t : ℝ) :
    i ≤ Module.finrank K ((ξ.minimaFiltration hd hm) t) ↔ (t : EReal) ≤ (ξ.logarithmicMinimum hd
        hm) i := by
  constructor
  · intro hi
    apply EReal.ge_of_forall_gt_iff_ge.mp
    intro u hu
    have hut : u < t := EReal.coe_lt_coe_iff.mp hu
    have hε : 0 < t - u := sub_pos.mpr hut
    have hr := hi.trans (Submodule.finrank_mono
      ((ξ.minimaFiltration_le_degreeThresholdSpan hd hm) t hε))
    have hb := (ξ.coe_le_logarithmicMinimum_of_finrank_le hd hm) hr
    convert hb using 1
    congr 1
    ring
  · intro ht
    obtain ⟨ε, hε, hΦ⟩ := (ξ.exists_minimaFiltration_eq_degreeThresholdSpan hd hm) t
    rw [hΦ]
    have hlt : ((t - ε : ℝ) : EReal) < (ξ.logarithmicMinimum hd hm) i :=
      (EReal.coe_lt_coe_iff.mpr (sub_lt_self t hε)).trans_le ht
    rw [logarithmicMinimum, lt_iSup_iff] at hlt
    obtain ⟨u, hu⟩ := hlt
    obtain ⟨hri, hu⟩ := lt_iSup_iff.mp hu
    exact hri.trans (Submodule.finrank_mono ((ξ.degreeThresholdSpan_antitone hd hm)
      (EReal.coe_lt_coe_iff.mp hu).le))

/-- The actual completed rank is detected by independent high-degree families
at every relaxed threshold. These families may depend on the relaxation. -/
theorem le_finrank_minimaFiltration_iff_forall_exists_linearIndependent
    (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (i : ℕ) (t : ℝ) :
    i ≤ Module.finrank K ((ξ.minimaFiltration hd hm) t) ↔
      ∀ ε : ℝ, 0 < ε → ∃ s : Fin i → {x : E // x ≠ 0},
        LinearIndependent K (fun j => (s j).val) ∧
        ∀ j, t - ε ≤ (ξ.vectorDegree hd hm) (s j) := by
  constructor
  · intro hi ε hε
    exact ((ξ.le_finrank_degreeThresholdSpan_iff hd hm) i (t - ε)).mp
      (hi.trans (Submodule.finrank_mono ((ξ.minimaFiltration_le_degreeThresholdSpan hd hm) t hε)))
  · intro h
    obtain ⟨ε, hε, hΦ⟩ := (ξ.exists_minimaFiltration_eq_degreeThresholdSpan hd hm) t
    rw [hΦ]
    exact ((ξ.le_finrank_degreeThresholdSpan_iff hd hm) i (t - ε)).mpr (h ε hε)

/-- A real filtration cut is zero exactly when it is above the first minimum.
This also holds for the rank-zero first-minimum convention. -/
theorem minimaFiltration_eq_bot_iff (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable) (t : ℝ) :
    (ξ.minimaFiltration hd hm) t = ⊥ ↔ (ξ.logarithmicMinimum hd hm) 1 < (t : EReal) := by
  constructor
  · intro hΦ
    apply lt_of_not_ge
    intro ht
    have hr := ((ξ.le_finrank_minimaFiltration_iff hd hm) 1 t).mpr ht
    rw [hΦ, finrank_bot] at hr
    omega
  · intro hmin
    apply Submodule.finrank_eq_zero.mp
    have hn : ¬ 1 ≤ Module.finrank K ((ξ.minimaFiltration hd hm) t) := by
      intro hr
      exact (not_le_of_gt hmin) (((ξ.le_finrank_minimaFiltration_iff hd hm) 1 t).mp hr)
    omega

/-- A real filtration cut is the whole space exactly when it is at most the
last minimum, including the rank-zero last-minimum convention. -/
theorem minimaFiltration_eq_top_iff (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm :
    ξ.IsMeasurable) (t : ℝ) :
    (ξ.minimaFiltration hd hm) t = ⊤ ↔
      (t : EReal) ≤ (ξ.logarithmicMinimum hd hm) (Module.finrank K E) := by
  constructor
  · intro hΦ
    apply ((ξ.le_finrank_minimaFiltration_iff hd hm) (Module.finrank K E) t).mp
    rw [hΦ, finrank_top]
  · intro ht
    have hr := ((ξ.le_finrank_minimaFiltration_iff hd hm) (Module.finrank K E) t).mpr ht
    exact Submodule.eq_top_of_finrank_eq (Nat.le_antisymm (Submodule.finrank_le _) hr)



/-- Literal rational sections of a completed restriction have exactly the
ambient vector degree. No restricted dual measurability is used. -/
theorem vectorDegree_restrict_eq (ξ : NormFamily S E) (hd : ξ.IsDominated)
    (hm : ξ.IsMeasurable) (U : Submodule K E) (s : {x : U // x ≠ 0}) :
    (ξ.restrict U).vectorDegree (hd.restrict U) (hm.restrict U) s =
      ξ.vectorDegree hd hm ⟨s.val.val, fun h => s.property (Subtype.ext h)⟩ := rfl


/-- The original analytic fields prove integrability of every actual restricted
rational section, independently of the restricted dual. -/
theorem integrable_restrict_logNorm (ξ : NormFamily S E) (hd : ξ.IsDominated)
    (hm : ξ.IsMeasurable) (U : Submodule K E) (x : U) :
    MeasureTheory.Integrable ((ξ.restrict U).logNorm x) S.v :=
  (hd.restrict U).integrable_logNorm (hm.restrict U) x

/-- Actual restricted threshold generators map to ambient threshold generators. -/
theorem degreeThresholdSpan_restrict_map_le (ξ : NormFamily S E)
    (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (U : Submodule K E) (t : ℝ) :
    ((ξ.restrict U).degreeThresholdSpan (hd.restrict U) (hm.restrict U) t).map U.subtype ≤
      ξ.degreeThresholdSpan hd hm t := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro x ⟨hx, ht⟩
  change (x : E) ∈ ξ.degreeThresholdSpan hd hm t
  have hne : (x : E) ≠ 0 := fun h => hx (Subtype.ext h)
  apply ξ.mem_degreeThresholdSpan hd hm ⟨x.val, hne⟩
  rw [← ξ.vectorDegree_restrict_eq hd hm U ⟨x, hx⟩]
  exact ht

/-- Literal completed restriction filtrations map into the ambient cut. -/
theorem minimaFiltration_restrict_map_le (ξ : NormFamily S E)
    (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (U : Submodule K E) (t : ℝ) :
    ((ξ.restrict U).minimaFiltration (hd.restrict U) (hm.restrict U) t).map U.subtype ≤
      ξ.minimaFiltration hd hm t := by
  apply le_iInf
  intro ε
  apply le_iInf
  intro hε
  exact (Submodule.map_mono
    ((ξ.restrict U).minimaFiltration_le_degreeThresholdSpan
      (hd.restrict U) (hm.restrict U) t hε)).trans
      (ξ.degreeThresholdSpan_restrict_map_le hd hm U (t - ε))

private theorem minimaFiltrationThresholdRefinement (ξ : NormFamily S E)
    (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      ξ.minimaFiltration hd hm t = ξ.degreeThresholdSpan hd hm (t - δ) := by
  obtain ⟨δ₀, hδ₀, hΦ⟩ := ξ.exists_minimaFiltration_eq_degreeThresholdSpan hd hm t
  have hδ : 0 < min δ₀ ε := lt_min hδ₀ hε
  refine ⟨min δ₀ ε, hδ, min_le_right _ _,
    le_antisymm (ξ.minimaFiltration_le_degreeThresholdSpan hd hm t hδ) ?_⟩
  exact (ξ.degreeThresholdSpan_antitone hd hm
    (sub_le_sub_left (min_le_left δ₀ ε) t)).trans hΦ.symm.le

/-- The literal restriction to the completed cut has last minimum at least
that cut, including the zero-space extended minimum. -/
theorem coe_le_minimalLogarithmicMinimum_restrict_minimaFiltration
    (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (t : ℝ) :
    (t : EReal) ≤
      (ξ.restrict (ξ.minimaFiltration hd hm t)).minimalLogarithmicMinimum
        (hd.restrict _) (hm.restrict _) := by
  classical
  let U := ξ.minimaFiltration hd hm t
  let R := ξ.restrict U
  apply (R.le_finrank_minimaFiltration_iff
    (hd.restrict U) (hm.restrict U) (Module.finrank K U) t).mp
  apply (R.le_finrank_minimaFiltration_iff_forall_exists_linearIndependent
    (hd.restrict U) (hm.restrict U) (Module.finrank K U) t).mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε, hΦ⟩ := minimaFiltrationThresholdRefinement ξ hd hm t hε
  have hr : Module.finrank K U ≤ Module.finrank K (ξ.degreeThresholdSpan hd hm (t - δ)) :=
    (congrArg (fun F : Submodule K E => Module.finrank K F) hΦ).le
  obtain ⟨s, hli, hs⟩ :=
    (ξ.le_finrank_degreeThresholdSpan_iff hd hm (Module.finrank K U) (t - δ)).mp hr
  let g : Fin (Module.finrank K U) → U := fun j => ⟨(s j).val, by
    change (s j).val ∈ ξ.minimaFiltration hd hm t
    rw [hΦ]
    exact ξ.mem_degreeThresholdSpan hd hm (s j) (hs j)⟩
  have hlig : LinearIndependent K g := LinearIndependent.of_comp U.subtype hli
  let f : Fin (Module.finrank K U) → {x : U // x ≠ 0} := fun j => ⟨g j, by
    intro h
    exact (s j).property (congrArg Subtype.val h)⟩
  refine ⟨f, hlig, ?_⟩
  intro j
  rw [ξ.vectorDegree_restrict_eq hd hm U]
  exact (sub_le_sub_left hδε t).trans (hs j)

/-- Intrinsic completed cuts are sums of actual nonzero subspaces with
restricted last minimum at least the cut. No restricted bundle is assumed. -/
theorem minimaFiltration_eq_iSup_restrict_minimalLogarithmicMinimum
    (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (t : ℝ) :
    ξ.minimaFiltration hd hm t =
      ⨆ (U : Submodule K E) (_ : U ≠ ⊥)
        (_ : (t : EReal) ≤ (ξ.restrict U).minimalLogarithmicMinimum
          (hd.restrict U) (hm.restrict U)), U := by
  classical
  apply le_antisymm
  · by_cases hΦ : ξ.minimaFiltration hd hm t = ⊥
    · rw [hΦ]
      exact bot_le
    · exact le_iSup_of_le (ξ.minimaFiltration hd hm t) (le_iSup_of_le hΦ (le_iSup_of_le
        (ξ.coe_le_minimalLogarithmicMinimum_restrict_minimaFiltration hd hm t) le_rfl))
  · apply iSup_le
    intro U
    apply iSup_le
    intro _
    apply iSup_le
    intro hmin
    have htop := ((ξ.restrict U).minimaFiltration_eq_top_iff
      (hd.restrict U) (hm.restrict U) t).mpr hmin
    have hmap := ξ.minimaFiltration_restrict_map_le hd hm U t
    rw [htop, Submodule.map_subtype_top] at hmap
    exact hmap

/-- Source 4.3.70's intrinsic formula on the literal completed restrictions.
All scalar fields and bases are allowed; rank zero uses an empty sum. -/
theorem minimaFiltration_eq_iInf_iSup_restrict_minimalLogarithmicMinimum
    (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (t : ℝ) :
    ξ.minimaFiltration hd hm t =
      ⨅ (ε : ℝ) (_ : 0 < ε),
        ⨆ (U : Submodule K E) (_ : U ≠ ⊥)
          (_ : ((t - ε : ℝ) : EReal) ≤
            (ξ.restrict U).minimalLogarithmicMinimum (hd.restrict U) (hm.restrict U)), U := by
  simp_rw [← ξ.minimaFiltration_eq_iSup_restrict_minimalLogarithmicMinimum hd hm]
  apply le_antisymm
  · apply le_iInf
    intro ε
    apply le_iInf
    intro hε
    exact ξ.minimaFiltration_antitone hd hm (sub_le_self t hε.le)
  · rw [ξ.minimaFiltration_eq_iInf_lt hd hm t]
    apply le_iInf
    intro u
    apply le_iInf
    intro hu
    have hε : 0 < t - u := sub_pos.mpr hu
    have h : (⨅ (ε : ℝ) (_ : 0 < ε), ξ.minimaFiltration hd hm (t - ε)) ≤
        ξ.minimaFiltration hd hm (t - (t - u)) :=
      iInf_le_of_le (t - u) (iInf_le_of_le hε le_rfl)
    convert h using 1
    congr 1
    ring

end
end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle
noncomputable section
universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The intrinsic actual threshold span is definitionally the bundle threshold span. -/
theorem degreeThresholdSpan_toNormFamily (V : AdelicVectorBundle S E) (t : ℝ) :
    V.toNormFamily.degreeThresholdSpan V.isDominated V.isMeasurable t =
      V.degreeThresholdSpan t := rfl

/-- The intrinsic extended minimum is definitionally the existing bundle minimum. -/
theorem logarithmicMinimum_toNormFamily (V : AdelicVectorBundle S E) (i : ℕ) :
    V.toNormFamily.logarithmicMinimum V.isDominated V.isMeasurable i =
      V.logarithmicMinimum i := rfl

/-- The intrinsic first minimum agrees with the existing first minimum. -/
theorem maximalLogarithmicMinimum_toNormFamily (V : AdelicVectorBundle S E) :
    V.toNormFamily.maximalLogarithmicMinimum V.isDominated V.isMeasurable =
      V.maximalLogarithmicMinimum := rfl

/-- The intrinsic last minimum agrees with the existing last minimum. -/
theorem minimalLogarithmicMinimum_toNormFamily (V : AdelicVectorBundle S E) :
    V.toNormFamily.minimalLogarithmicMinimum V.isDominated V.isMeasurable =
      V.minimalLogarithmicMinimum := rfl

/-- The intrinsic completed filtration agrees with the existing bundle filtration. -/
theorem minimaFiltration_toNormFamily (V : AdelicVectorBundle S E) (t : ℝ) :
    V.toNormFamily.minimaFiltration V.isDominated V.isMeasurable t =
      V.minimaFiltration t := rfl

/-- Any available genuine restriction has the same intrinsic threshold span. -/
theorem degreeThresholdSpan_restrict_toNormFamily (V : AdelicVectorBundle S E)
    (U : Submodule K E) (hmDual : (V.toNormFamily.restrict U).dual.IsMeasurable) (t : ℝ) :
    (V.toNormFamily.restrict U).degreeThresholdSpan
      (V.isDominated.restrict U) (V.isMeasurable.restrict U) t =
        (V.restrict U hmDual).degreeThresholdSpan t := rfl

/-- Any available genuine restriction has the same intrinsic ordinary minima. -/
theorem logarithmicMinimum_restrict_toNormFamily (V : AdelicVectorBundle S E)
    (U : Submodule K E) (hmDual : (V.toNormFamily.restrict U).dual.IsMeasurable) (i : ℕ) :
    (V.toNormFamily.restrict U).logarithmicMinimum
      (V.isDominated.restrict U) (V.isMeasurable.restrict U) i =
        (V.restrict U hmDual).logarithmicMinimum i := rfl

/-- Any available genuine restriction has the same intrinsic last minimum. -/
theorem minimalLogarithmicMinimum_restrict_toNormFamily (V : AdelicVectorBundle S E)
    (U : Submodule K E) (hmDual : (V.toNormFamily.restrict U).dual.IsMeasurable) :
    (V.toNormFamily.restrict U).minimalLogarithmicMinimum
      (V.isDominated.restrict U) (V.isMeasurable.restrict U) =
        (V.restrict U hmDual).minimalLogarithmicMinimum := rfl

/-- Any available genuine restriction has the same intrinsic completed filtration. -/
theorem minimaFiltration_restrict_toNormFamily (V : AdelicVectorBundle S E)
    (U : Submodule K E) (hmDual : (V.toNormFamily.restrict U).dual.IsMeasurable) (t : ℝ) :
    (V.toNormFamily.restrict U).minimaFiltration
      (V.isDominated.restrict U) (V.isMeasurable.restrict U) t =
        (V.restrict U hmDual).minimaFiltration t := rfl

/-- The original actual bundle filtration has the full intrinsic restriction
formula without any measurable-base or restricted-dual constructor hypothesis. -/
theorem minimaFiltration_eq_iInf_iSup_intrinsic_restrict_minimalLogarithmicMinimum
    (V : AdelicVectorBundle S E) (t : ℝ) :
    V.minimaFiltration t =
      ⨅ (ε : ℝ) (_ : 0 < ε),
        ⨆ (U : Submodule K E) (_ : U ≠ ⊥)
          (_ : ((t - ε : ℝ) : EReal) ≤
            (V.toNormFamily.restrict U).minimalLogarithmicMinimum
              (V.isDominated.restrict U) (V.isMeasurable.restrict U)), U :=
  V.toNormFamily.minimaFiltration_eq_iInf_iSup_restrict_minimalLogarithmicMinimum
    V.isDominated V.isMeasurable t

end
end ArakelovGeometry.AdelicVectorBundle

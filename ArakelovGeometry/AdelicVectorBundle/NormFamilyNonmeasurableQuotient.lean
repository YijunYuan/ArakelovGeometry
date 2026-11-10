/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicStructure.TrivialPlace
public import ArakelovGeometry.AdelicVectorBundle.Measurable
public import ArakelovGeometry.AdelicVectorBundle.Quotient
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A measurable norm family with a nonmeasurable quotient

The actual real trivial-completion plane in Chen–Moriwaki Remark 4.1.23.
A fixed parameter set changes the cheap-line norm between one half and one.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NonmeasurableQuotientCounterexample

open AdelicStructure

local instance : DecidablePred (fun x : ℝ => x = 0) :=
  fun _ => Classical.propDecidable _

open Classical in
/-- The source's Borel real parameter space with Lebesgue measure and
constant trivial absolute value. -/
abbrev curve : AdelicStructure ℝ where
  Ω := ℝ
  A := inferInstance
  v := volume
  ϕ := fun _ => AbsoluteValue.trivial
  measurable_log := (trivialAdelicStructure ℝ ℝ volume).measurable_log
  integrable_log := (trivialAdelicStructure ℝ ℝ volume).integrable_log

abbrev Plane := ℝ × ℝ

open Classical in
/-- The positive weight detects membership in the chosen arbitrary set. -/
def weight (B : Set ℝ) (t : ℝ) : ℝ := if t ∈ B then 1 / 2 else 1

theorem weight_pos (B : Set ℝ) (t : ℝ) : 0 < weight B t := by
  classical
  simp only [weight]
  split_ifs <;> norm_num

theorem weight_le_one (B : Set ℝ) (t : ℝ) : weight B t ≤ 1 := by
  classical
  simp only [weight]
  split_ifs <;> norm_num

open Classical in
/-- A varying cheap line in the original real plane. -/
def rawNorm (B : Set ℝ) (t : ℝ) (x : Plane) : ℝ :=
  if x = 0 then 0 else if x.2 = t * x.1 then weight B t else 1

@[simp]
theorem rawNorm_zero (B : Set ℝ) (t : ℝ) : rawNorm B t 0 = 0 := by
  simp [rawNorm]

theorem rawNorm_le_one (B : Set ℝ) (t : ℝ) (x : Plane) : rawNorm B t x ≤ 1 := by
  classical
  simp only [rawNorm]
  split_ifs <;> first | exact weight_le_one B t | norm_num

theorem half_le_rawNorm (B : Set ℝ) (t : ℝ) {x : Plane} (hx : x ≠ 0) :
    (1 / 2 : ℝ) ≤ rawNorm B t x := by
  classical
  simp only [rawNorm, ite_eq_right hx, weight]
  split_ifs <;> norm_num

theorem rawNorm_eq_zero_iff (B : Set ℝ) (t : ℝ) (x : Plane) :
    rawNorm B t x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · exact iff_of_false (ne_of_gt (lt_of_lt_of_le (by norm_num) (half_le_rawNorm B t hx))) hx

/-- The weighted plane norm satisfies the triangle inequality. -/
theorem rawNorm_add_le (B : Set ℝ) (t : ℝ) (x y : Plane) :
    rawNorm B t (x + y) ≤ rawNorm B t x + rawNorm B t y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  linarith [rawNorm_le_one B t (x + y), half_le_rawNorm B t hx, half_le_rawNorm B t hy]

open Classical in
private theorem rawNorm_smul (B : Set ℝ) (t c : ℝ) (x : Plane) :
    rawNorm B t (c • x) = (AbsoluteValue.trivial : AbsoluteValue ℝ ℝ) c * rawNorm B t x := by
  by_cases hc : c = 0
  · simp [hc]
  rw [AbsoluteValue.trivial_apply hc, one_mul]
  by_cases hx : x = 0
  · simp [hx]
  have hcx : c • x ≠ 0 := (smul_eq_zero_iff_right hc).not.mpr hx
  have hline : c * x.2 = t * (c * x.1) ↔ x.2 = t * x.1 := by
    rw [mul_left_comm t c x.1]
    exact ⟨mul_left_cancel₀ hc, fun h => congrArg (c * ·) h⟩
  simp only [rawNorm, ite_eq_right hcx, ite_eq_right hx, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, hline]

open Classical in
/-- A separating seminorm over the trivially normed original field. -/
def localSeminorm (B : Set ℝ) (t : ℝ) :
    Seminorm (WithAbs (AbsoluteValue.trivial : AbsoluteValue ℝ ℝ)) Plane :=
  Seminorm.of (rawNorm B t) (rawNorm_add_le B t) (by
    intro c x
    change rawNorm B t (c.ofAbs • x) = ‖c‖ * rawNorm B t x
    rw [WithAbs.norm_eq_apply_ofAbs]
    exact rawNorm_smul B t c.ofAbs x)

open Classical in
/-- The actual source norm family on the completed tensor fibres. -/
def normFamily (B : Set ℝ) : NormFamily curve Plane where
  norm t := by
    change Seminorm (AbsoluteValue.trivial : AbsoluteValue ℝ ℝ).Completion
      ((AbsoluteValue.trivial : AbsoluteValue ℝ ℝ).Completion ⊗[ℝ] Plane)
    exact Seminorm.of (fun z => localSeminorm B t (trivialCompletedTensorEquiv ℝ Plane z))
      (by intro x y; rw [map_add]; exact map_add_le_add (localSeminorm B t) _ _)
      (by
        intro c z
        rw [trivialCompletedTensorEquiv_smul]
        change localSeminorm B t
          (WithAbs.toAbs (AbsoluteValue.trivial : AbsoluteValue ℝ ℝ)
            (trivialCompletionAlgEquiv ℝ c) • trivialCompletedTensorEquiv ℝ Plane z) = _
        rw [map_smul_eq_mul, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_toAbs,
          ← norm_trivialCompletion ℝ c])
  norm_eq_zero_iff t z := by
    change rawNorm B t (trivialCompletedTensorEquiv ℝ Plane z) = 0 ↔ z = 0
    rw [rawNorm_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

open Classical in
@[simp]
theorem normFamily_norm_rational (B : Set ℝ) (t : curve.Ω) (x : Plane) :
    (normFamily B).norm t ((1 : (curve.ϕ t).Completion) ⊗ₜ[ℝ] x) = rawNorm B t x := by
  change rawNorm B t (trivialCompletedTensorEquiv ℝ Plane (1 ⊗ₜ[ℝ] x)) = _
  rw [trivialCompletedTensorEquiv_one_tmul]

/-- The source cheap-line norm is ultrametric, for an arbitrary parameter set. -/
theorem rawNorm_add_le_max (B : Set ℝ) (t : ℝ) (x y : Plane) :
    rawNorm B t (x + y) ≤ max (rawNorm B t x) (rawNorm B t y) := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  by_cases hxl : x.2 = t * x.1
  · by_cases hyl : y.2 = t * y.1
    · have hsl : (x + y).2 = t * (x + y).1 := by
        simp only [Prod.fst_add, Prod.snd_add, hxl, hyl, mul_add]
      by_cases hs : x + y = 0
      · rw [hs, rawNorm_zero]
        exact le_max_of_le_left (by
          rw [rawNorm, ite_eq_right hx, ite_eq_left hxl]
          exact (weight_pos B t).le)
      · simp only [rawNorm, ite_eq_right hx, ite_eq_right hy, ite_eq_right hs, ite_eq_left hxl,
          ite_eq_left hyl, ite_eq_left hsl, max_self, le_refl]
    · simpa only [rawNorm, ite_eq_right hx, ite_eq_right hy, ite_eq_left hxl, ite_eq_right hyl,
        max_eq_right (weight_le_one B t)] using rawNorm_le_one B t (x + y)
  · by_cases hyl : y.2 = t * y.1
    · simpa only [rawNorm, ite_eq_right hx, ite_eq_right hy, ite_eq_right hxl, ite_eq_left hyl,
        max_eq_left (weight_le_one B t)] using rawNorm_le_one B t (x + y)
    · simpa only [rawNorm, ite_eq_right hx, ite_eq_right hy, ite_eq_right hxl, ite_eq_right hyl,
        max_self] using rawNorm_le_one B t (x + y)

/-- Actual completed fibres inherit the ultrametric inequality. -/
theorem normFamily_isUltrametric (B : Set ℝ) : (normFamily B).IsUltrametric := by
  intro t _ z y
  change rawNorm B t (trivialCompletedTensorEquiv ℝ Plane (z + y)) ≤
    max (rawNorm B t (trivialCompletedTensorEquiv ℝ Plane z))
      (rawNorm B t (trivialCompletedTensorEquiv ℝ Plane y))
  rw [map_add]
  exact rawNorm_add_le_max B t _ _

/-- Each fixed rational vector has a Borel evaluation, despite the arbitrary
choice of parameter set: its norm can vary at only one parameter. -/
theorem normFamily_isMeasurable (B : Set ℝ) : (normFamily B).IsMeasurable := by
  classical
  intro x
  change Measurable (fun t : ℝ => rawNorm B t
    (trivialCompletedTensorEquiv ℝ Plane (1 ⊗ₜ[ℝ] x)))
  simp only [trivialCompletedTensorEquiv_one_tmul]
  by_cases hx : x = 0
  · simpa only [hx, rawNorm_zero] using (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ)))
  by_cases hx1 : x.1 = 0
  · have hn (t : ℝ) : rawNorm B t x = 1 := by
      have hx2 : x.2 ≠ 0 := fun h => hx (Prod.ext hx1 h)
      simp [rawNorm, hx, hx1, hx2]
    simpa only [hn] using (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ)))
  let c := x.2 / x.1
  have hn (t : ℝ) : rawNorm B t x = if t = c then weight B c else 1 := by
    have hl : x.2 = t * x.1 ↔ t = c := by
      dsimp [c]
      exact ⟨fun h => (eq_div_iff hx1).mpr h.symm,
        fun h => ((eq_div_iff hx1).mp h).symm⟩
    simp only [rawNorm, ite_eq_right hx, hl]
    split_ifs with ht
    · rw [ht]
    · rfl
  have hm : Measurable (fun t : ℝ => if t = c then weight B c else 1) :=
    Measurable.ite (measurableSet_singleton c) measurable_const measurable_const
  simpa only [hn] using hm

/-- The quotient map has precisely the vertical line as kernel. -/
def projection : Plane →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ

theorem projection_surjective : Function.Surjective projection :=
  fun a => ⟨(a, 0), rfl⟩

/-- The genuine quotient norm family along the first coordinate. -/
def quotientFamily (B : Set ℝ) : NormFamily curve ℝ :=
  (normFamily B).pushforward projection projection_surjective

private theorem weight_le_rawNorm (B : Set ℝ) (t : ℝ) {x : Plane} (hx : x ≠ 0) :
    weight B t ≤ rawNorm B t x := by
  classical
  simp only [rawNorm, ite_eq_right hx]
  split_ifs
  · exact le_rfl
  · exact weight_le_one B t

/-- Every completed plane vector is the rational pure tensor given by its
canonical trivial-completion coordinates. -/
theorem eq_one_tmul_trivialCoordinates (t : curve.Ω)
    (z : (curve.ϕ t).Completion ⊗[ℝ] Plane) :
    z = (1 : (curve.ϕ t).Completion) ⊗ₜ[ℝ] trivialCompletedTensorEquiv ℝ Plane z := by
  apply (trivialCompletedTensorEquiv ℝ Plane).injective
  rw [trivialCompletedTensorEquiv_one_tmul]

/-- The canonical quotient infimum is attained by the moving cheap-line lift. -/
theorem quotientFamily_norm_one (B : Set ℝ) (t : curve.Ω) :
    (quotientFamily B).norm t ((1 : (curve.ϕ t).Completion) ⊗ₜ[ℝ] (1 : ℝ)) =
      weight B t := by
  apply le_antisymm
  · have h := (normFamily B).pushforward_norm_le projection projection_surjective t
      ((1 : (curve.ϕ t).Completion) ⊗ₜ[ℝ] ((1, t) : Plane))
    rw [LinearMap.baseChange_tmul, normFamily_norm_rational] at h
    simpa [quotientFamily, projection, rawNorm] using h
  · apply ((normFamily B).le_quotientSeminorm_iff projection projection_surjective t _ _).mpr
    intro z hz
    let x := trivialCompletedTensorEquiv ℝ Plane z
    have hzx := eq_one_tmul_trivialCoordinates t z
    have hx : x.1 = 1 := by
      rw [hzx, LinearMap.baseChange_tmul] at hz
      have h := congrArg (trivialCompletedTensorEquiv ℝ ℝ) hz
      simpa only [trivialCompletedTensorEquiv_one_tmul, projection, LinearMap.fst_apply] using h
    have hx0 : x ≠ 0 := by
      intro h
      have h0 := congrArg Prod.fst h
      simp only [hx, Prod.fst_zero] at h0
      exact one_ne_zero h0
    change weight B t ≤ rawNorm B t x
    exact weight_le_rawNorm B t hx0

/-- Non-Borel input is detected by an actual quotient evaluation. -/
theorem quotientFamily_not_isMeasurable (B : Set ℝ) (hB : ¬ MeasurableSet B) :
    ¬ (quotientFamily B).IsMeasurable := by
  classical
  intro h
  have hm : Measurable (weight B) := by
    have hm := h (1 : ℝ)
    have he : (fun t : curve.Ω => (quotientFamily B).norm t
        ((1 : (curve.ϕ t).Completion) ⊗ₜ[ℝ] (1 : ℝ))) = weight B :=
      funext (quotientFamily_norm_one B)
    rw [he] at hm
    exact hm
  have he : (weight B) ⁻¹' {1 / 2} = B := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, weight]
    split_ifs <;> simp_all
  exact hB (he ▸ hm (measurableSet_singleton (1 / 2 : ℝ)))

/-- A countable Borel generator and Cantor's theorem produce an actual
non-Borel parameter set; no nonmeasurability hypothesis is assumed. -/
theorem exists_nonBorel_set : ∃ B : Set ℝ, ¬ MeasurableSet B := by
  classical
  by_contra h
  have hall : ∀ B : Set ℝ, MeasurableSet B := by simpa only [not_exists, not_not] using h
  let g : Set (Set ℝ) := Set.range (fun q : ℚ => Set.Iio (q : ℝ))
  have hgen : (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom g := by
    simpa only [Set.iUnion_singleton_eq_range] using
      (BorelSpace.measurable_eq (α := ℝ)).trans Real.borel_eq_generateFrom_Iio_rat
  have hg : Cardinal.mk g ≤ Cardinal.continuum := by
    exact (Set.countable_range (fun q : ℚ => Set.Iio (q : ℝ))).le_aleph0.trans
      Cardinal.aleph0_le_continuum
  have hcard : Cardinal.mk {B : Set ℝ // MeasurableSet B} ≤ Cardinal.continuum := by
    have hc := MeasurableSpace.cardinal_measurableSet_le_continuum hg
    exact (congrArg (fun m : MeasurableSpace ℝ =>
      Cardinal.mk {B : Set ℝ // @MeasurableSet ℝ m B}) hgen).le.trans hc
  have hsurj : Function.Surjective (Subtype.val : {B : Set ℝ // MeasurableSet B} → Set ℝ) :=
    fun B => ⟨⟨B, hall B⟩, rfl⟩
  have hbig := (Cardinal.mk_le_of_surjective hsurj).trans hcard
  rw [Cardinal.mk_set, Cardinal.mk_real] at hbig
  exact (not_le_of_gt (Cardinal.cantor Cardinal.continuum)) hbig

/-- An actual measurable ultrametric norm family on the source's Borel real
adelic curve has an actual nonmeasurable one-dimensional quotient. -/
theorem exists_measurable_normFamily_nonmeasurable_quotient :
    ∃ B : Set ℝ, (normFamily B).IsMeasurable ∧ (normFamily B).IsUltrametric ∧
      ¬ (quotientFamily B).IsMeasurable := by
  obtain ⟨B, hB⟩ := exists_nonBorel_set
  exact ⟨B, normFamily_isMeasurable B, normFamily_isUltrametric B,
    quotientFamily_not_isMeasurable B hB⟩

end ArakelovGeometry.NonmeasurableQuotientCounterexample

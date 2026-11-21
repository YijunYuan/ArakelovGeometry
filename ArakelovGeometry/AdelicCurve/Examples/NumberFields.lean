/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Defs
public import ArakelovGeometry.Analysis.AbsoluteValue.Ostrowski
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# The number-field adelic curve

Each place `ω : Place K` is represented by its normalized absolute value `placeRep ω`:
the mathlib `FinitePlace` value for nonarchimedean places, the `InfinitePlace` value for
archimedean places, and the trivial absolute value for the trivial place. The measure gives
a nonarchimedean place mass `1`, an archimedean place mass `mult` (`1` or `2`), and the
trivial place mass `0`. With this normalization, properness of the resulting adelic
curve is exactly the product formula `NumberField.prod_abs_eq_one`.

The integrability obligation `integrable_log` reduces, via the Dirac-sum criterion
`MeasureTheory.integrable_sum_dirac_iff`, to summability of
`ω ↦ (placeWeight ω).toReal * ‖log (placeRep ω x)‖`, which has finite support by
`finite_out_ne_one` (transported along `ω.out ≈ placeRep ω`).
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure

open MeasureTheory AbsoluteValue NumberField
open scoped ENNReal

section PlaceData

variable {K : Type*} [Field K] [NumberField K]

/-- A finite place takes a value `< 1` at some nonzero element (any nonzero element of its
maximal ideal). -/
theorem finitePlace_exists_lt_one (v : FinitePlace K) : ∃ y : K, y ≠ 0 ∧ v y < 1 := by
  obtain ⟨a, ha_mem, ha_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
  refine ⟨algebraMap (𝓞 K) K a, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha_ne
  · have h := (FinitePlace.norm_lt_one_iff_mem (K := K) (v := v.maximalIdeal) (x := a)).mpr
      ha_mem
    rwa [FinitePlace.norm_embedding_eq] at h

/-- The class of a finite place is not the trivial place. -/
theorem mk_finitePlace_ne_trivialPlace (v : FinitePlace K) :
    (Quotient.mk' v.val : AbsoluteValue.Place K) ≠ trivialPlace K := by
  classical
  intro h
  obtain ⟨y, hy0, hy1⟩ := finitePlace_exists_lt_one v
  have hequiv : v.val ≈ (AbsoluteValue.trivial : AbsoluteValue K ℝ) := Quotient.eq'.mp h
  have heq : v.val = (AbsoluteValue.trivial : AbsoluteValue K ℝ) :=
    isEquiv_trivial_iff_eq_trivial.mp hequiv
  have h1 : v y = 1 := by
    rw [FinitePlace.coe_apply, heq]
    exact AbsoluteValue.trivial_apply hy0
  rw [h1] at hy1
  exact lt_irrefl 1 hy1

/-- The class of a finite place is nonarchimedean. -/
theorem isNonarchimedeanPlace_mk_finitePlace (v : FinitePlace K) :
    IsNonarchimedeanPlace (Quotient.mk' v.val : AbsoluteValue.Place K) := by
  have hout : (Quotient.mk' v.val : AbsoluteValue.Place K).out ≈ v.val :=
    Quotient.mk_out (s := AbsoluteValue.instSetoid) v.val
  exact (isNonarchimedean_congr (hout : _root_.AbsoluteValue.IsEquiv _ _)).mpr
    (finitePlace_isNonarchimedean v)

omit [NumberField K] in
/-- An infinite place takes the value `2` at `2`. -/
theorem infinitePlace_apply_two (w : InfinitePlace K) : w ((2 : ℕ) : K) = 2 := by
  rw [← InfinitePlace.norm_embedding_eq, map_natCast]
  simp

/-- The class of an infinite place is not the trivial place. -/
theorem mk_infinitePlace_ne_trivialPlace (w : InfinitePlace K) :
    (Quotient.mk' w.val : AbsoluteValue.Place K) ≠ trivialPlace K := by
  classical
  intro h
  have hequiv : w.val ≈ (AbsoluteValue.trivial : AbsoluteValue K ℝ) := Quotient.eq'.mp h
  have heq : w.val = (AbsoluteValue.trivial : AbsoluteValue K ℝ) :=
    isEquiv_trivial_iff_eq_trivial.mp hequiv
  have h2 : w ((2 : ℕ) : K) = 1 := by
    rw [InfinitePlace.coe_apply, heq]
    exact AbsoluteValue.trivial_apply
      (Nat.cast_ne_zero.mpr (by norm_num : (2 : ℕ) ≠ 0))
  rw [infinitePlace_apply_two w] at h2
  norm_num at h2

/-- The class of an infinite place is archimedean. -/
theorem not_isNonarchimedeanPlace_mk_infinitePlace (w : InfinitePlace K) :
    ¬IsNonarchimedeanPlace (Quotient.mk' w.val : AbsoluteValue.Place K) := by
  intro hna
  have hout : (Quotient.mk' w.val : AbsoluteValue.Place K).out ≈ w.val :=
    Quotient.mk_out (s := AbsoluteValue.instSetoid) w.val
  exact infinitePlace_not_isNonarchimedean w
    ((isNonarchimedean_congr (hout : _root_.AbsoluteValue.IsEquiv _ _)).mp hna)

open Classical in
/-- The canonical (normalized) representative of a place: the trivial absolute value for the
trivial place, the mathlib `FinitePlace` value for nonarchimedean places, the mathlib
`InfinitePlace` value for archimedean ones. -/
noncomputable def placeRep (ω : AbsoluteValue.Place K) : AbsoluteValue K ℝ :=
  if hp : ω = trivialPlace K then .trivial
  else if hna : IsNonarchimedeanPlace ω then ((isNonarchimedeanPlace_iff ω hp).mp hna).choose.val
  else ((isArchimedeanPlace_iff ω).mp hna).choose.val

open Classical in
/-- The weight of a place in the number-field adelic structure: `0` for the trivial place,
`1` for nonarchimedean places, `mult` (`1` or `2`) for archimedean places. -/
noncomputable def placeWeight (ω : AbsoluteValue.Place K) : ℝ≥0∞ :=
  if ω = trivialPlace K then 0
  else if hna : IsNonarchimedeanPlace ω then 1
  else (((isArchimedeanPlace_iff ω).mp hna).choose.mult : ℝ≥0∞)

/-- The weight of a place is finite. -/
theorem placeWeight_ne_top (ω : AbsoluteValue.Place K) : placeWeight ω ≠ ∞ := by
  rw [placeWeight]
  split_ifs
  · exact ENNReal.zero_ne_top
  · exact ENNReal.one_ne_top
  · exact ENNReal.natCast_ne_top _

/-- The trivial place has weight zero. -/
theorem placeWeight_trivialPlace : placeWeight (trivialPlace K) = 0 := by
  rw [placeWeight, ite_eq_left rfl]

/-- Every representative choice is equivalent to the canonical one. -/
theorem placeRep_equiv (ω : AbsoluteValue.Place K) : ω.out ≈ placeRep ω := by
  rw [placeRep]
  split_ifs with h1 h2
  · rw [h1, trivialPlace_out_eq]
  · exact ((isNonarchimedeanPlace_iff ω h1).mp h2).choose_spec
  · exact ((isArchimedeanPlace_iff ω).mp h2).choose_spec

/-- The finite place chosen by the classification at the class of `v` is `v` itself. -/
theorem finitePlace_choose_eq (v : FinitePlace K)
    (hp : (Quotient.mk' v.val : AbsoluteValue.Place K) ≠ trivialPlace K)
    (hna : IsNonarchimedeanPlace (Quotient.mk' v.val : AbsoluteValue.Place K)) :
    ((isNonarchimedeanPlace_iff (Quotient.mk' v.val) hp).mp hna).choose = v := by
  have hspec := ((isNonarchimedeanPlace_iff (Quotient.mk' v.val) hp).mp hna).choose_spec
  have hout : (Quotient.mk' v.val : AbsoluteValue.Place K).out ≈ v.val :=
    Quotient.mk_out (s := AbsoluteValue.instSetoid) v.val
  apply finitePlace_injective_place
  exact Quotient.sound' ((Setoid.symm hspec).trans hout)

/-- The infinite place chosen by the classification at the class of `w` is `w` itself. -/
theorem infinitePlace_choose_eq (w : InfinitePlace K)
    (hna : ¬IsNonarchimedeanPlace (Quotient.mk' w.val : AbsoluteValue.Place K)) :
    ((isArchimedeanPlace_iff (Quotient.mk' w.val)).mp hna).choose = w := by
  have hspec := ((isArchimedeanPlace_iff (Quotient.mk' w.val)).mp hna).choose_spec
  have hout : (Quotient.mk' w.val : AbsoluteValue.Place K).out ≈ w.val :=
    Quotient.mk_out (s := AbsoluteValue.instSetoid) w.val
  rw [InfinitePlace.eq_iff_isEquiv]
  exact (Setoid.symm hspec).trans hout

/-- The canonical representative of the class of a finite place is that finite place. -/
theorem placeRep_mk_finitePlace (v : FinitePlace K) :
    placeRep (Quotient.mk' v.val : AbsoluteValue.Place K) = v.val := by
  unfold placeRep
  split_ifs with h1 h2
  · exact absurd h1 (mk_finitePlace_ne_trivialPlace v)
  · exact congrArg Subtype.val (finitePlace_choose_eq v h1 h2)
  · exact absurd (isNonarchimedeanPlace_mk_finitePlace v) h2

/-- The class of a finite place has weight `1`. -/
theorem placeWeight_mk_finitePlace (v : FinitePlace K) :
    placeWeight (Quotient.mk' v.val : AbsoluteValue.Place K) = 1 := by
  unfold placeWeight
  split_ifs with h1 h2
  · exact absurd h1 (mk_finitePlace_ne_trivialPlace v)
  · rfl
  · exact absurd (isNonarchimedeanPlace_mk_finitePlace v) h2

/-- The canonical representative of the class of an infinite place is that infinite
place. -/
theorem placeRep_mk_infinitePlace (w : InfinitePlace K) :
    placeRep (Quotient.mk' w.val : AbsoluteValue.Place K) = w.val := by
  unfold placeRep
  split_ifs with h1 h2
  · exact absurd h1 (mk_infinitePlace_ne_trivialPlace w)
  · exact absurd h2 (not_isNonarchimedeanPlace_mk_infinitePlace w)
  · exact congrArg Subtype.val (infinitePlace_choose_eq w h2)

/-- The class of an infinite place has weight `mult` (`1` or `2`). -/
theorem placeWeight_mk_infinitePlace (w : InfinitePlace K) :
    placeWeight (Quotient.mk' w.val : AbsoluteValue.Place K) = (w.mult : ℝ≥0∞) := by
  unfold placeWeight
  split_ifs with h1 h2
  · exact absurd h1 (mk_infinitePlace_ne_trivialPlace w)
  · exact absurd h2 (not_isNonarchimedeanPlace_mk_infinitePlace w)
  · rw [infinitePlace_choose_eq w h2]

/-- Every place is the trivial place, the class of a finite place, or the class of an
infinite place. -/
theorem place_trichotomy (ω : AbsoluteValue.Place K) :
    ω = trivialPlace K ∨ (∃ v : FinitePlace K, ω = Quotient.mk' v.val) ∨
      ∃ w : InfinitePlace K, ω = Quotient.mk' w.val := by
  by_cases hp : ω = trivialPlace K
  · exact Or.inl hp
  rcases isNonarchimedeanPlace_or_isArchimedeanPlace ω with hna | harch
  · obtain ⟨v, hv⟩ := (isNonarchimedeanPlace_iff ω hp).mp hna
    refine Or.inr (Or.inl ⟨v, ?_⟩)
    rw [← Quotient.out_eq ω]
    exact Quotient.sound hv
  · obtain ⟨w, hw⟩ := (isArchimedeanPlace_iff ω).mp harch
    refine Or.inr (Or.inr ⟨w, ?_⟩)
    rw [← Quotient.out_eq ω]
    exact Quotient.sound hw

end PlaceData

/-- The adelic structure of a number field `K`: the places of `K` with the counting-type
measure weighted by `placeWeight`, each place represented by its normalized absolute value
`placeRep`. -/
noncomputable def numberFieldAdelicStructure (K : Type*) [Field K] [NumberField K] :
    AdelicStructure K where
  Ω := AbsoluteValue.Place K
  A := ⊤
  v := by
    letI : MeasurableSpace (AbsoluteValue.Place K) := ⊤
    exact Measure.sum (fun a ↦ placeWeight a • Measure.dirac a)
  ϕ := placeRep
  measurable_log := fun x _ ↦ measurable_from_top
  integrable_log := by
    intro x hx
    let : MeasurableSpace (AbsoluteValue.Place K) := ⊤
    -- The Dirac-sum integrability criterion, with weights `placeWeight` and `x = id`.
    have hiff := integrable_sum_dirac_iff (ι := AbsoluteValue.Place K)
      (X := AbsoluteValue.Place K) (E := ℝ) (x := id)
      (c := placeWeight)
      (f := fun ω ↦ Real.log ((placeRep ω) x))
      placeWeight_ne_top
    refine hiff.mpr ?_
    apply summable_of_hasFiniteSupport
    -- The support is contained in the finite set `{ω | ω.out x ≠ 1}`.
    apply Set.Finite.subset (finite_out_ne_one (K := K) hx)
    intro ω hω
    simp only [Function.mem_support, id_eq, Set.mem_ofPred_eq] at hω ⊢
    -- If `ω.out x = 1`, then `placeRep ω x = 1` too, so the summand is `0`.
    intro hc
    apply hω
    have h1 : placeRep ω x = 1 :=
      ((placeRep_equiv ω : ω.out.IsEquiv (placeRep ω)).eq_one_iff).mp hc
    rw [h1, Real.log_one, norm_zero, mul_zero]

/-- The **product formula** `NumberField.prod_abs_eq_one` in logarithmic form,
integrated against the place measure of the number-field adelic structure. -/
theorem numberField_product_formula {K : Type*} [Field K] [NumberField K] {x : K}
    (hx : x ≠ 0) :
    letI : MeasurableSpace (AbsoluteValue.Place K) := ⊤
    ∫ ω, Real.log ((placeRep (K := K) ω) x)
      ∂(Measure.sum fun ω : AbsoluteValue.Place K ↦ placeWeight ω • Measure.dirac ω)
      = 0 := by
  let : MeasurableSpace (AbsoluteValue.Place K) := ⊤
  classical
  -- Step 1: the integral is the weighted sum of `log (placeRep ω x)` over all places.
  have hint : ∫ ω, Real.log ((placeRep (K := K) ω) x)
      ∂(Measure.sum fun ω : AbsoluteValue.Place K ↦ placeWeight ω • Measure.dirac ω)
      = ∑' ω : AbsoluteValue.Place K, (placeWeight ω).toReal • Real.log ((placeRep ω) x) :=
    integral_sum_dirac (X := AbsoluteValue.Place K) (E := ℝ) (x := id)
      (c := placeWeight) (f := fun ω ↦ Real.log ((placeRep ω) x)) placeWeight_ne_top
  -- Step 2: the sum vanishes, by the product formula.
  have hSfin : (Function.mulSupport fun v : FinitePlace K ↦ v x).Finite :=
    FinitePlace.hasFiniteMulSupport hx
  have key : (∑' ω : AbsoluteValue.Place K,
      (placeWeight ω).toReal • Real.log ((placeRep ω) x)) = 0 := by
    set g : AbsoluteValue.Place K → ℝ :=
      fun ω ↦ (placeWeight ω).toReal • Real.log ((placeRep ω) x) with hg
    set Sinf : Finset (AbsoluteValue.Place K) :=
      Finset.univ.image (fun w : InfinitePlace K ↦ Quotient.mk' w.val) with hSinfDef
    set Sfin : Finset (AbsoluteValue.Place K) :=
      hSfin.toFinset.image (fun v : FinitePlace K ↦ Quotient.mk' v.val) with hSfinDef
    -- `g` vanishes off `Sinf ∪ Sfin`.
    have hvanish : ∀ ω ∉ Sinf ∪ Sfin, g ω = 0 := by
      intro ω hω
      rcases place_trichotomy ω with h | ⟨v, rfl⟩ | ⟨w, rfl⟩
      · subst h
        change (placeWeight _).toReal • Real.log ((placeRep _) x) = 0
        rw [placeWeight_trivialPlace]
        simp
      · -- a nonarchimedean place outside `Sfin` satisfies `v x = 1`
        have hv1 : v x = 1 := by
          by_contra hne
          exact hω (Finset.mem_union_right _ (by
            rw [hSfinDef]
            exact Finset.mem_image.mpr
              ⟨v, hSfin.mem_toFinset.mpr (Function.mem_mulSupport.mpr hne), rfl⟩))
        change (placeWeight _).toReal • Real.log ((placeRep _) x) = 0
        rw [placeRep_mk_finitePlace v, show v.val x = v x from rfl, hv1, Real.log_one,
          smul_zero]
      · -- archimedean places are all in `Sinf`
        exact absurd (Finset.mem_union_left _ (by
          rw [hSinfDef]
          exact Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩)) hω
    rw [tsum_eq_sum hvanish]
    -- `Sinf` and `Sfin` are disjoint (archimedean vs nonarchimedean).
    have hdisj : Disjoint Sinf Sfin := by
      rw [Finset.disjoint_left]
      rintro a ha hb
      rw [hSinfDef] at ha
      rw [hSfinDef] at hb
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, -, hvw⟩ := Finset.mem_image.mp hb
      have hequiv : v.val ≈ w.val := Quotient.eq'.mp hvw
      exact infinitePlace_not_isNonarchimedean w
        ((isNonarchimedean_congr hequiv).mp (finitePlace_isNonarchimedean v))
    rw [Finset.sum_union hdisj]
    -- reindex the two parts by `InfinitePlace K` and by the support of the finite part
    have hIinj : ∀ w₁ ∈ (Finset.univ : Finset (InfinitePlace K)), ∀ w₂ ∈ Finset.univ,
        (Quotient.mk' w₁.val : AbsoluteValue.Place K) = Quotient.mk' w₂.val → w₁ = w₂ := by
      intro w₁ _ w₂ _ h
      rw [InfinitePlace.eq_iff_isEquiv]
      exact Quotient.eq'.mp h
    have hFinj : ∀ v₁ ∈ hSfin.toFinset, ∀ v₂ ∈ hSfin.toFinset,
        (Quotient.mk' v₁.val : AbsoluteValue.Place K) = Quotient.mk' v₂.val → v₁ = v₂ :=
      fun v₁ _ v₂ _ h ↦ finitePlace_injective_place h
    have h5 := Finset.sum_image (f := g) (s := (Finset.univ : Finset (InfinitePlace K)))
      (g := fun w : InfinitePlace K ↦ (Quotient.mk' w.val : AbsoluteValue.Place K))
      (fun w₁ hw₁ w₂ hw₂ h ↦ hIinj w₁ hw₁ w₂ hw₂ h)
    have h6 := Finset.sum_image (f := g) (s := hSfin.toFinset)
      (g := fun v : FinitePlace K ↦ (Quotient.mk' v.val : AbsoluteValue.Place K))
      (fun v₁ hv₁ v₂ hv₂ h ↦ hFinj v₁ hv₁ v₂ hv₂ h)
    rw [hSinfDef, hSfinDef, h5, h6]
    -- evaluate the summands via the canonical representatives
    have e1 : ∀ w : InfinitePlace K,
        g (Quotient.mk' w.val) = (w.mult : ℝ) * Real.log (w x) := by
      intro w
      change (placeWeight _).toReal • Real.log ((placeRep _) x) = _
      rw [placeRep_mk_infinitePlace w, placeWeight_mk_infinitePlace w,
        ENNReal.toReal_natCast, smul_eq_mul]
      rfl
    have e2 : ∀ v : FinitePlace K, g (Quotient.mk' v.val) = Real.log (v x) := by
      intro v
      change (placeWeight _).toReal • Real.log ((placeRep _) x) = _
      rw [placeRep_mk_finitePlace v, placeWeight_mk_finitePlace v, ENNReal.toReal_one,
        one_smul]
      rfl
    simp only [e1, e2]
    -- the product formula in logarithmic form
    have hwne : ∀ w : InfinitePlace K, w x ≠ 0 := fun w =>
      ne_of_gt (InfinitePlace.pos_iff.mpr hx)
    have hvne : ∀ v : FinitePlace K, v x ≠ 0 := fun v =>
      ne_of_gt (FinitePlace.pos_iff.mpr hx)
    have hA : ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w x)
        = Real.log (∏ w : InfinitePlace K, (w x) ^ w.mult) := by
      rw [Real.log_prod (fun w _ ↦ pow_ne_zero _ (hwne w))]
      exact Finset.sum_congr rfl fun w _ ↦ (Real.log_pow _ _).symm
    have hBrw : (∏ᶠ v : FinitePlace K, v x) = ∏ v ∈ hSfin.toFinset, v x := by
      apply finprod_eq_prod_of_mulSupport_subset
      rw [Set.Finite.coe_toFinset]
    have hB : ∑ v ∈ hSfin.toFinset, Real.log (v x)
        = Real.log (∏ᶠ v : FinitePlace K, v x) := by
      rw [hBrw, Real.log_prod (fun v _ ↦ hvne v)]
    rw [hA, hB, ← Real.log_mul
      (Finset.prod_ne_zero_iff.mpr fun w _ ↦ pow_ne_zero _ (hwne w))
      (by rw [hBrw]; exact Finset.prod_ne_zero_iff.mpr fun v _ ↦ hvne v),
      prod_abs_eq_one hx, Real.log_one]
  exact hint.trans key

/-- The number-field adelic structure is proper by the logarithmic form of the
**product formula** `NumberField.prod_abs_eq_one`. -/
instance instIsProperNumberFieldAdelicStructure (K : Type*) [Field K] [NumberField K] :
    IsProper (numberFieldAdelicStructure K) := by
  constructor
  intro x hx
  exact numberField_product_formula (K := K) (x := x) hx

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.AdelicCurve

open NumberField

/-- The adelic curve of a number field `K`. -/
noncomputable abbrev numberFieldAdelicCurve (K : Type*) [Field K] [NumberField K] :
    AdelicCurve :=
  (AdelicStructure.numberFieldAdelicStructure K).toAdelicCurve

/-- The logarithmic product formula, exposed in the curve namespace for compatibility. -/
alias numberField_product_formula := AdelicStructure.numberField_product_formula

/-- Properness of the number-field adelic curve, inherited from its adelic structure. -/
abbrev instIsProperNumberFieldAdelicCurve (K : Type*) [Field K] [NumberField K] :
    IsProper (numberFieldAdelicCurve K) :=
  AdelicStructure.instIsProperNumberFieldAdelicStructure K

end ArakelovGeometry.AdelicCurve

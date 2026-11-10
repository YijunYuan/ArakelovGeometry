/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NormFamilyActualPrimeIndexing
public import ArakelovGeometry.NumberTheory.NormalizedNumberFieldCurve

/-!
# Comparing the actual normalized and ideal-norm product formulas

The actual normalized curve is already proper. Finite support and its actual
singleton masses convert that product formula to a weighted place sum.
-/

@[expose] public section

open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K] [NumberField K]

/-- The actual normalized value is equivalent to the quotient's representative. -/
theorem normalizedPlaceValue_isEquiv_out
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    ω.val.out.IsEquiv (normalizedPlaceValue ω) := by
  rw [← normalizedPlaceValue_class ω]
  exact Quotient.mk_out (normalizedPlaceValue ω)

/-- Nonzero evaluations of the actual normalized values have finite multiplicative support. -/
theorem normalizedPlaceValue_hasFiniteMulSupport {a : K} (ha : a ≠ 0) :
    (Function.mulSupport fun ω :
      {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} =>
      normalizedPlaceValue ω a).Finite := by
  have hs : (Subtype.val ⁻¹' {ω : AbsoluteValue.Place K | ω.out a ≠ 1} :
      Set {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}).Finite :=
    (finite_out_ne_one (K := K) ha).preimage Subtype.val_injective.injOn
  apply hs.subset
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  intro hone
  exact hω ((normalizedPlaceValue_isEquiv_out ω).eq_one_iff.mp hone)

/-- The actual completion-degree weighted logarithms are summable without an ef formula. -/
theorem normalizedPlaceValue_weightedLog_summable {a : K} (ha : a ≠ 0) :
    Summable (fun ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} =>
      ((normalizedPlaceValue ω).localDegree ℚ : ℝ) * Real.log (normalizedPlaceValue ω a)) := by
  apply summable_of_hasFiniteSupport
  apply (normalizedPlaceValue_hasFiniteMulSupport ha).subset
  intro ω hω
  simp only [Function.mem_support, Function.mem_mulSupport] at hω ⊢
  intro hone
  exact hω (by rw [hone, Real.log_one, mul_zero])

/-- The actual normalized product formula as a sum over completion-degree atoms. -/
theorem normalizedNumberField_weighted_product_formula {a : K} (ha : a ≠ 0) :
    (∑' ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K},
      ((normalizedPlaceValue ω).localDegree ℚ : ℝ) * Real.log (normalizedPlaceValue ω a)) =
      0 := by
  have h := (normalizedNumberFieldAdelicStructure_isProper (K := K)).product_formula a ha
  let μ : Measure {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} :=
    (normalizedNumberFieldAdelicStructure K).v
  change (∫ ω, Real.log (normalizedPlaceValue ω a) ∂μ) = 0 at h
  rw [← Measure.sum_smul_dirac μ] at h
  have hint : (∫ ω, Real.log (normalizedPlaceValue ω a)
      ∂(Measure.sum fun ω => μ {ω} • Measure.dirac ω)) =
      ∑' ω, (μ {ω}).toReal * Real.log (normalizedPlaceValue ω a) := by
    simpa only [id_eq, smul_eq_mul] using
      (integral_sum_dirac (x := id) (c := fun ω => μ {ω})
        (f := fun ω => Real.log (normalizedPlaceValue ω a)) (fun ω => by
          change (normalizedNumberFieldAdelicStructure K).v {ω} ≠ ⊤
          rw [normalizedNumberFieldAdelicStructure_v_singleton]
          exact ENNReal.natCast_ne_top _))
  rw [hint] at h
  have hweight (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
      (μ {ω}).toReal = ((normalizedPlaceValue ω).localDegree ℚ : ℝ) := by
    calc
      (μ {ω}).toReal = ((normalizedNumberFieldAdelicStructure K).v {ω}).toReal := rfl
      _ = (((normalizedPlaceValue ω).localDegree ℚ : ENNReal)).toReal :=
        congrArg ENNReal.toReal (normalizedNumberFieldAdelicStructure_v_singleton ω)
      _ = _ := ENNReal.toReal_natCast _
  calc
    _ = ∑' ω, (μ {ω}).toReal * Real.log (normalizedPlaceValue ω a) :=
      tsum_congr fun ω => congrArg (fun t => t * Real.log (normalizedPlaceValue ω a))
        (hweight ω).symm
    _ = 0 := h

/-- The old weighted logarithms remain summable on the actual nontrivial classes. -/
theorem numberField_nontrivial_weightedLog_summable {a : K} (ha : a ≠ 0) :
    Summable (fun ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} =>
      (placeWeight ω.val).toReal * Real.log (placeRep ω.val a)) := by
  apply summable_of_hasFiniteSupport
  have hs : (Subtype.val ⁻¹' {ω : AbsoluteValue.Place K | ω.out a ≠ 1} :
      Set {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}).Finite :=
    (finite_out_ne_one (K := K) ha).preimage Subtype.val_injective.injOn
  apply hs.subset
  intro ω hω
  simp only [Function.mem_support, Set.mem_preimage, Set.mem_ofPred_eq] at hω ⊢
  intro hone
  exact hω (by rw [(placeRep_equiv ω.val).eq_one_iff.mp hone, Real.log_one, mul_zero])

/-- Deleting the zero-mass trivial point preserves the old product formula. -/
theorem numberField_nontrivial_weighted_product_formula {a : K} (ha : a ≠ 0) :
    (∑' ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K},
      (placeWeight ω.val).toReal * Real.log (placeRep ω.val a)) = 0 := by
  let : MeasurableSpace (AbsoluteValue.Place K) := ⊤
  have hint : (∫ ω : AbsoluteValue.Place K, Real.log (placeRep ω a)
      ∂Measure.sum fun ω => placeWeight ω • Measure.dirac ω) =
      ∑' ω : AbsoluteValue.Place K, (placeWeight ω).toReal * Real.log (placeRep ω a) := by
    simpa only [id_eq, smul_eq_mul] using
      (integral_sum_dirac (x := id) (c := placeWeight)
        (f := fun ω => Real.log (placeRep ω a)) placeWeight_ne_top)
  have hfull : (∑' ω : AbsoluteValue.Place K,
      (placeWeight ω).toReal * Real.log (placeRep ω a)) = 0 := by
    exact hint.symm.trans (numberField_product_formula (K := K) ha)
  apply (tsum_subtype_eq_of_support_subset ?_).trans hfull
  intro ω hω
  simp only [Function.mem_support] at hω
  intro heq
  subst ω
  exact hω (by rw [placeWeight_trivialPlace]; simp)

/-- The actual normalized value is equivalent to the old representative of its place. -/
theorem normalizedPlaceValue_isEquiv_placeRep
    (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) :
    (normalizedPlaceValue ω).IsEquiv (placeRep ω.val) :=
  (normalizedPlaceValue_isEquiv_out ω).symm.trans (placeRep_equiv ω.val)

/-- The two produced product formulas identify the logarithm at an isolated finite prime. -/
theorem normalizedPlaceValue_isolated_finitePlace_log
    (v : FinitePlace K) {a : K} (ha : a ≠ 0)
    (hfinite : ∀ q : FinitePlace K, q ≠ v → q a = 1) :
    ((normalizedPlaceValue ⟨Quotient.mk' v.val,
      mk_finitePlace_ne_trivialPlace v⟩).localDegree ℚ : ℝ) *
      Real.log (normalizedPlaceValue ⟨Quotient.mk' v.val,
        mk_finitePlace_ne_trivialPlace v⟩ a) = Real.log (v a) := by
  classical
  let ωv : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} :=
    ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩
  let gnew (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) : ℝ :=
    ((normalizedPlaceValue ω).localDegree ℚ : ℝ) * Real.log (normalizedPlaceValue ω a)
  let gold (ω : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}) : ℝ :=
    (placeWeight ω.val).toReal * Real.log (placeRep ω.val a)
  have hz : (∑' ω, (gnew ω - gold ω)) = 0 := by
    rw [(normalizedPlaceValue_weightedLog_summable ha).tsum_sub
      (numberField_nontrivial_weightedLog_summable ha),
      normalizedNumberField_weighted_product_formula ha,
      numberField_nontrivial_weighted_product_formula ha, sub_self]
  have hdifference : (∑' ω, (gnew ω - gold ω)) = gnew ωv - gold ωv := by
    apply tsum_eq_single ωv
    intro ω hω
    rcases place_trichotomy ω.val with ht | ⟨q, hq⟩ | ⟨w, hw⟩
    · exact (ω.property ht).elim
    · have hqv : q ≠ v := by
        intro heq
        apply hω
        apply Subtype.ext
        simpa only [ωv, heq] using hq
      have holdone : placeRep ω.val a = 1 := by
        rw [hq, placeRep_mk_finitePlace]
        exact hfinite q hqv
      have hnewone : normalizedPlaceValue ω a = 1 :=
        (normalizedPlaceValue_isEquiv_placeRep ω).eq_one_iff.mpr holdone
      simp only [gnew, gold, hnewone, holdone, Real.log_one, mul_zero, sub_self]
    · have hωw : ω = ⟨Quotient.mk' w.val, mk_infinitePlace_ne_trivialPlace w⟩ :=
        Subtype.ext hw
      have hvalue : normalizedPlaceValue ω = w.val := by
        rw [hωw]
        exact normalizedPlaceValue_eq_infinitePlace w
      have hdegree : (normalizedPlaceValue ω).localDegree ℚ = w.mult :=
        (congrArg (fun b : AbsoluteValue K ℝ => b.localDegree ℚ) hvalue).trans
          w.localDegree_rat
      have hweight : placeWeight ω.val = (w.mult : ENNReal) := by
        rw [hw]
        exact placeWeight_mk_infinitePlace w
      have holdvalue : placeRep ω.val = w.val := by
        rw [hw]
        exact placeRep_mk_infinitePlace w
      dsimp only [gnew, gold]
      rw [hdegree, hvalue, hweight, holdvalue, ENNReal.toReal_natCast, sub_self]
  have h := hdifference.symm.trans hz
  change ((normalizedPlaceValue ωv).localDegree ℚ : ℝ) *
    Real.log (normalizedPlaceValue ωv a) -
    (placeWeight (Quotient.mk' v.val)).toReal * Real.log (placeRep (Quotient.mk' v.val) a)
      = 0 at h
  rw [placeWeight_mk_finitePlace, placeRep_mk_finitePlace,
    ENNReal.toReal_one, one_mul] at h
  exact sub_eq_zero.mp h

/-- A genuine isolated element forces the positive equivalence exponent to be the actual
completion degree; no ramification or residue-degree identity is assumed. -/
theorem normalizedPlaceValue_rpow_localDegree_of_isolated_finitePlace
    (v : FinitePlace K) {a : K} (ha : a ≠ 0) (hv : v a < 1)
    (hfinite : ∀ q : FinitePlace K, q ≠ v → q a = 1) (x : K) :
    (normalizedPlaceValue ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩ x) ^
      ((normalizedPlaceValue ⟨Quotient.mk' v.val,
        mk_finitePlace_ne_trivialPlace v⟩).localDegree ℚ : ℝ) = v x := by
  let ωv : {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K} :=
    ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩
  let α : AbsoluteValue K ℝ := normalizedPlaceValue ωv
  have hequiv : α.IsEquiv v.val :=
    Quotient.eq'.mp (normalizedPlaceValue_class ωv)
  obtain ⟨t, ht, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  have hpos : 0 < α a := α.pos ha
  have hne : α a ≠ 1 := by
    intro hone
    exact (ne_of_lt hv) (hequiv.eq_one_iff.mp hone)
  have hlog : t * Real.log (α a) = Real.log (v a) := by
    have h := congrArg Real.log (congrFun hpow a)
    rwa [Real.log_rpow hpos t] at h
  have hprod : (α.localDegree ℚ : ℝ) * Real.log (α a) = Real.log (v a) :=
    normalizedPlaceValue_isolated_finitePlace_log v ha hfinite
  have htd : t = (α.localDegree ℚ : ℝ) :=
    mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one hpos hne)
      (hlog.trans hprod.symm)
  change (α x) ^ (α.localDegree ℚ : ℝ) = v x
  rw [← htd]
  exact congrFun hpow x

/-- Every actual normalized finite value has precisely the actual completion-degree power
giving the ideal-norm value. The needed isolated integer is produced. -/
theorem normalizedPlaceValue_rpow_localDegree_finitePlace (v : FinitePlace K) (x : K) :
    (normalizedPlaceValue ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩ x) ^
      ((normalizedPlaceValue ⟨Quotient.mk' v.val,
        mk_finitePlace_ne_trivialPlace v⟩).localDegree ℚ : ℝ) = v x := by
  obtain ⟨f, hf, hv, hfinite⟩ := ActualPrimeIndexing.exists_integral_isolated_finitePlace K v
  have hfK : algebraMap (𝓞 K) K f ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hf
  exact normalizedPlaceValue_rpow_localDegree_of_isolated_finitePlace v hfK hv hfinite x

/-- The actual completed degree at every finite normalized value is positive. -/
theorem normalizedPlaceValue_finitePlace_localDegree_pos (v : FinitePlace K) :
    0 < (normalizedPlaceValue ⟨Quotient.mk' v.val,
      mk_finitePlace_ne_trivialPlace v⟩).localDegree ℚ := by
  by_contra hn
  have hd := Nat.eq_zero_of_not_pos hn
  have h := normalizedPlaceValue_rpow_localDegree_finitePlace v (0 : K)
  rw [hd, Nat.cast_zero, Real.rpow_zero, map_zero] at h
  exact one_ne_zero h

/-- Weighted logarithms agree pointwise at every actual finite place. -/
theorem normalizedPlaceValue_weightedLog_finitePlace (v : FinitePlace K)
    {x : K} (hx : x ≠ 0) :
    ((normalizedPlaceValue ⟨Quotient.mk' v.val,
      mk_finitePlace_ne_trivialPlace v⟩).localDegree ℚ : ℝ) *
      Real.log (normalizedPlaceValue ⟨Quotient.mk' v.val,
        mk_finitePlace_ne_trivialPlace v⟩ x) = Real.log (v x) := by
  have h := congrArg Real.log (normalizedPlaceValue_rpow_localDegree_finitePlace v x)
  rwa [Real.log_rpow ((normalizedPlaceValue _).pos hx)] at h

/-- The produced finite normalized value is the inverse actual-degree power of the
ideal-norm value, including evaluation at zero. -/
theorem normalizedPlaceValue_eq_finitePlace_rpow (v : FinitePlace K) (x : K) :
    normalizedPlaceValue ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩ x =
      (v x) ^ (((normalizedPlaceValue ⟨Quotient.mk' v.val,
        mk_finitePlace_ne_trivialPlace v⟩).localDegree ℚ : ℝ)⁻¹) := by
  let α : AbsoluteValue K ℝ := normalizedPlaceValue
    ⟨Quotient.mk' v.val, mk_finitePlace_ne_trivialPlace v⟩
  have hd : (α.localDegree ℚ : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (normalizedPlaceValue_finitePlace_localDegree_pos v))
  calc
    α x = (α x) ^ ((α.localDegree ℚ : ℝ) * (α.localDegree ℚ : ℝ)⁻¹) := by
      rw [mul_inv_cancel₀ hd, Real.rpow_one]
    _ = ((α x) ^ (α.localDegree ℚ : ℝ)) ^ (α.localDegree ℚ : ℝ)⁻¹ :=
      Real.rpow_mul (α.nonneg x) _ _
    _ = (v x) ^ (α.localDegree ℚ : ℝ)⁻¹ :=
      congrArg (fun t : ℝ => t ^ (α.localDegree ℚ : ℝ)⁻¹)
        (normalizedPlaceValue_rpow_localDegree_finitePlace v x)

end ArakelovGeometry.AdelicStructure

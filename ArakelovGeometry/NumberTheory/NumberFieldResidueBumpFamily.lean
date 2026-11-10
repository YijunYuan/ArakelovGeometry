/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.ResidueDirectionBump
import ArakelovGeometry.NumberTheory.NumberFieldResidueDirectionSelection
import ArakelovGeometry.AdelicVectorBundle.NormFamilyCompletionNumberField
import ArakelovGeometry.AdelicVectorBundle.NumberFieldMeasurable

/-!
# An actual dominated residue-bump family on the normalized rational curve

The expensive directions use the selected actual prime completions. Each fixed
rational vector meets only finitely many of them, while the completed dual
family is unchanged. This is the family for the corrected Remark 4.1.36.
-/

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldResidueDirection

open NormFamily ResidueDirectionBump

/-- The standard basis of the original rational plane. -/
def basis : Module.Basis (Fin 2) ℚ Plane := Module.Basis.finTwoProd ℚ

/-- The accepted strongly dominated mixed coordinate reference. -/
def referenceFamily : NormFamily S Plane := ofBasisMixed S Plane basis

theorem referenceFamily_strong : referenceFamily.IsStronglyDominated :=
  ofBasisMixed_isStronglyDominated basis
    AdelicStructure.normalizedNumberFieldArchimedeanCompletions

/-- Coordinates use the actual scalar extension of the rational basis. -/
def coordinates (ω : S.Ω) : ((S.ϕ ω).Completion ⊗[ℚ] Plane) ≃ₗ[(S.ϕ ω).Completion]
    ((S.ϕ ω).Completion × (S.ϕ ω).Completion) :=
  (basis.baseChange (S.ϕ ω).Completion).equivFun.trans
    (LinearEquiv.finTwoArrow (S.ϕ ω).Completion (S.ϕ ω).Completion)

@[simp] theorem coordinates_one_tmul (ω : S.Ω) (z : Plane) :
    coordinates ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[ℚ] z) =
      (algebraMap ℚ (S.ϕ ω).Completion z.1, algebraMap ℚ (S.ϕ ω).Completion z.2) := by
  ext <;> simp [coordinates, basis, Algebra.smul_def,
    Module.Basis.equivFun_apply, Module.Basis.coe_finTwoProd_repr]

theorem referenceFamily_norm_finite (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[ℚ] Plane) : referenceFamily.norm ω z = ‖coordinates ω z‖ := by
  rw [referenceFamily, ofBasisMixed_norm_of_finite basis ω hω, ofBasis_norm]
  let c := (basis.baseChange (S.ϕ ω).Completion).equivFun z
  change ‖c‖ = max ‖c 0‖ ‖c 1‖
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg ((_root_.norm_nonneg _).trans (le_max_left _ _))).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (norm_le_pi_norm c 0) (norm_le_pi_norm c 1)

private def bumpSeminorm (ω : S.Ω) (hω : ω ∈ S.Ωfin) (a : ℚ) (ha : S.ϕ ω a = 1) :
    Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[ℚ] Plane) := by
  letI := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (S.norm_add_le_max_of_finite ω hω)
  exact (planeSeminorm (algebraMap ℚ (S.ϕ ω).Completion a)
    (by rw [S.norm_algebraMap_eq_absValue, ha])).comp (coordinates ω).toLinearMap

private theorem bumpSeminorm_apply (ω : S.Ω) (hω : ω ∈ S.Ωfin) (a : ℚ)
    (ha : S.ϕ ω a = 1) (z : (S.ϕ ω).Completion ⊗[ℚ] Plane) :
    bumpSeminorm ω hω a ha z = value
      (slopeFunctional (algebraMap ℚ (S.ϕ ω).Completion a)) (coordinates ω z) := rfl

private theorem bumpSeminorm_zero (ω : S.Ω) (hω : ω ∈ S.Ωfin) (a : ℚ)
    (ha : S.ϕ ω a = 1) (z : (S.ϕ ω).Completion ⊗[ℚ] Plane) :
    bumpSeminorm ω hω a ha z = 0 ↔ z = 0 := by
  rw [bumpSeminorm_apply, value_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

/-- The actual norm family: expensive selected residue directions, reference elsewhere. -/
def family : NormFamily S Plane := by
  classical
  exact {
    norm := fun ω ↦ if h : ∃ n, point n = ω then
      bumpSeminorm ω (h.choose_spec ▸ point_mem_fin h.choose) (slope h.choose)
        (by simpa only [h.choose_spec] using slope_unit h.choose)
      else referenceFamily.norm ω
    norm_eq_zero_iff := fun ω z ↦ by
      split_ifs
      · exact bumpSeminorm_zero _ _ _ _ _
      · exact referenceFamily.norm_eq_zero_iff _ _ }

theorem family_norm_of_notMem_range (ω : S.Ω) (hω : ω ∉ Set.range point)
    (z : (S.ϕ ω).Completion ⊗[ℚ] Plane) : family.norm ω z = referenceFamily.norm ω z := by
  change ¬∃ n, point n = ω at hω
  simp only [family, dif_neg hω]

theorem family_norm_point (n : ℕ) (z : (S.ϕ (point n)).Completion ⊗[ℚ] Plane) :
    family.norm (point n) z = value
      (slopeFunctional (algebraMap ℚ (S.ϕ (point n)).Completion (slope n)))
      (coordinates (point n) z) := by
  classical
  have h : ∃ m, point m = point n := ⟨n, rfl⟩
  have hc : h.choose = n := point_injective h.choose_spec
  simp only [family, dif_pos h, bumpSeminorm_apply, hc]

/-- Every original norm is bounded above by the bumped norm at the same completed vector. -/
theorem referenceFamily_le_family (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[ℚ] Plane) :
    referenceFamily.norm ω z ≤ family.norm ω z := by
  by_cases h : ω ∈ Set.range point
  · obtain ⟨n, rfl⟩ := h
    rw [family_norm_point, referenceFamily_norm_finite _ (point_mem_fin n)]
    exact norm_le_value _ _
  · rw [family_norm_of_notMem_range ω h]

/-- The complete fibrewise comparison keeps the inflation below two. -/
theorem family_le_two_mul_reference (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[ℚ] Plane) :
    family.norm ω z ≤ 2 * referenceFamily.norm ω z := by
  by_cases h : ω ∈ Set.range point
  · obtain ⟨n, rfl⟩ := h
    rw [family_norm_point, referenceFamily_norm_finite _ (point_mem_fin n)]
    exact value_le_two_mul_norm _ _
  · rw [family_norm_of_notMem_range ω h]
    linarith [referenceFamily.norm_nonneg ω z]

/-- The selected unit axes remain unit vectors in every actual completed fibre. -/
theorem family_norm_basis (ω : S.Ω) (i : Fin 2) :
    family.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[ℚ] basis i) = 1 := by
  by_cases h : ω ∈ Set.range point
  · obtain ⟨n, rfl⟩ := h
    rw [family_norm_point, coordinates_one_tmul]
    fin_cases i
    · have hu := (S.norm_algebraMap_eq_absValue (point n) (slope n)).trans (slope_unit n)
      have hu' : (1 : ℝ) ≤ ‖(slope n : (S.ϕ (point n)).Completion)‖ :=
        le_of_eq (by simpa using hu.symm)
      simpa [basis, value, Prod.norm_def] using hu'
    · simp [basis, value, Prod.norm_def]
  · rw [family_norm_of_notMem_range ω h]
    exact (ofBasisMixed_norm_tmul_basis basis ω 1 i).trans norm_one

/-- The actual completed operator dual is unchanged, at all places and on all dual vectors. -/
theorem family_dual_eq_reference_dual : family.dual = referenceFamily.dual := by
  ext ω f
  apply le_antisymm
  · exact referenceFamily.dual_norm_antitone family ω
      (referenceFamily_le_family ω) f
  · rw [referenceFamily, ofBasisMixed_dual_norm]
    apply (pi_norm_le_iff_of_nonneg (family.dual.norm_nonneg ω f)).mpr
    intro i
    have h := family.norm_dual_apply_le ω f
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[ℚ] basis i)
    simpa only [Module.Basis.baseChange_apply, family_norm_basis, mul_one] using h

/-- The literal rational-vector bump test uses the actual normalized prime absolute value. -/
theorem family_norm_rational_point (n : ℕ) (z : Plane) :
    family.norm (point n) ((1 : (S.ϕ (point n)).Completion) ⊗ₜ[ℚ] z) =
      if S.ϕ (point n) (z.2 - slope n * z.1) <
          max (S.ϕ (point n) z.1) (S.ϕ (point n) z.2) then
        2 * max (S.ϕ (point n) z.1) (S.ϕ (point n) z.2)
      else max (S.ϕ (point n) z.1) (S.ϕ (point n) z.2) := by
  rw [family_norm_point, coordinates_one_tmul]
  simp only [value, slopeFunctional_apply, Prod.norm_def, ← map_mul, ← map_sub,
    S.norm_algebraMap_eq_absValue]

/-- Each rational vector's logarithmic change has actual finite support. -/
theorem finite_logNorm_difference_support (z : Plane) :
    (Function.support (fun ω ↦ family.logNorm z ω - referenceFamily.logNorm z ω)).Finite := by
  apply (finite_expensive_places z).subset
  intro ω hω
  by_contra hnot
  apply hω
  change family.logNorm z ω - referenceFamily.logNorm z ω = 0
  apply sub_eq_zero.mpr
  unfold logNorm
  congr 1
  by_cases h : ω ∈ Set.range point
  · obtain ⟨n, rfl⟩ := h
    have hn : ¬S.ϕ (point n) (z.2 - slope n * z.1) <
        max (S.ϕ (point n) z.1) (S.ϕ (point n) z.2) :=
      fun hh ↦ hnot ⟨n, rfl, hh⟩
    rw [family_norm_rational_point, if_neg hn,
      referenceFamily_norm_finite _ (point_mem_fin n), coordinates_one_tmul, Prod.norm_def,
      S.norm_algebraMap_eq_absValue, S.norm_algebraMap_eq_absValue]
  · exact family_norm_of_notMem_range ω h _

/-- The actual standard-number-field family is dominated in the source's primal/dual sense. -/
theorem family_isDominated : family.IsDominated := by
  constructor
  · intro z hz
    have hd : Integrable (fun ω ↦ family.logNorm z ω - referenceFamily.logNorm z ω) S.v :=
      integrable_normalized_of_finiteSupport _ (finite_logNorm_difference_support z)
    have hb : HasIntegrableUpperBound
        (fun ω ↦ family.logNorm z ω - referenceFamily.logNorm z ω) S.v :=
      ⟨_, hd, Filter.Eventually.of_forall fun _ ↦ le_rfl⟩
    apply ((referenceFamily_strong.isDominated.1 z hz).add hb).mono
    exact Filter.Eventually.of_forall fun ω ↦ by dsimp; linarith
  · rw [family_dual_eq_reference_dual]
    exact referenceFamily_strong.isDominated.2

/-- A genuine adelic vector bundle with the original residue-bump completed norms. -/
def bundle : AdelicVectorBundle S Plane :=
  AdelicVectorBundle.ofDominatedNumberField family family_isDominated

/-- Every selected actual place contributes at least the fixed positive logarithmic distance. -/
theorem log_two_le_localDist_point (n : ℕ) :
    Real.log 2 ≤ family.localDist referenceFamily (point n) := by
  have hξ : family.norm (point n)
      ((1 : (S.ϕ (point n)).Completion) ⊗ₜ[ℚ] ((1, slope n) : Plane)) = 2 := by
    simp [family_norm_rational_point, slope_unit]
  have hβ : referenceFamily.norm (point n)
      ((1 : (S.ϕ (point n)).Completion) ⊗ₜ[ℚ] ((1, slope n) : Plane)) = 1 := by
    rw [referenceFamily_norm_finite _ (point_mem_fin n), coordinates_one_tmul,
      Prod.norm_def, S.norm_algebraMap_eq_absValue, S.norm_algebraMap_eq_absValue]
    simp [slope_unit]
  have h := family.log_norm_sub_le_localDist referenceFamily (point n)
    ((1 : (S.ϕ (point n)).Completion) ⊗ₜ[ℚ] ((1, slope n) : Plane))
  rw [hξ, hβ, Real.log_one, sub_zero] at h
  exact (le_abs_self _).trans h

/-- Positive actual completion-degree atoms all have mass at least one. -/
theorem one_le_singleton_mass (ω : S.Ω) : (1 : ENNReal) ≤ S.v {ω} := by
  have hp := ActualPrimeIndexing.normalized_singleton_pos ω
  have hm : S.v {ω} = ((AdelicStructure.normalizedPlaceValue ω).localDegree ℚ : ENNReal) :=
    AdelicStructure.normalizedNumberFieldAdelicStructure_v_singleton ω
  have hp' := hp.trans_eq hm
  have hd : 0 < (AdelicStructure.normalizedPlaceValue ω).localDegree ℚ := by
    exact_mod_cast hp'
  apply le_trans _ hm.ge
  exact_mod_cast Nat.succ_le_of_lt hd

private instance : MeasurableSingletonClass S.Ω :=
  inferInstanceAs (MeasurableSingletonClass
    {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})

private instance : DiscreteMeasurableSpace S.Ω :=
  inferInstanceAs (DiscreteMeasurableSpace
    {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})

/-- The selected genuine prime-place locus has infinite measure in the standard curve. -/
theorem measure_range_point : S.v (Set.range point) = ⊤ := by
  have hr : Set.range point = ⋃ n : ℕ, ({point n} : Set S.Ω) := by ext; simp
  rw [hr, measure_iUnion]
  · apply top_unique
    calc
      ⊤ = ∑' _ : ℕ, (1 : ENNReal) := (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
      _ ≤ ∑' n : ℕ, S.v {point n} := ENNReal.tsum_le_tsum fun n ↦ one_le_singleton_mass _
  · intro n m hnm
    exact Set.disjoint_singleton.mpr (fun h ↦ hnm (point_injective h))
  · intro n
    exact measurableSet_singleton _

/-- No integrable upper envelope exists for the actual source local-distance function. -/
theorem localDist_not_hasIntegrableUpperBound :
    ¬ HasIntegrableUpperBound (family.localDist referenceFamily) S.v := by
  classical
  rintro ⟨g, hg, hbound⟩
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let f : S.Ω → ℝ := (Set.range point).indicator (fun _ ↦ Real.log 2)
  have hf : Integrable f S.v := by
    apply hg.mono' (show Measurable f from Measurable.of_discrete).aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    by_cases h : ω ∈ Set.range point
    · obtain ⟨n, rfl⟩ := h
      simpa only [f, Set.indicator_of_mem (Set.mem_range_self n),
        Real.norm_eq_abs, abs_of_pos hp] using (log_two_le_localDist_point n).trans hω
    · simpa only [f, Set.indicator_of_notMem h, _root_.norm_zero] using
        (family.localDist_nonneg referenceFamily ω).trans hω
  have hfin := ((integrableOn_const_iff (C := Real.log 2) (by finiteness)).mp
    ((integrable_indicator_iff MeasurableSet.of_discrete).mp hf))
  rcases hfin with hz | hm
  · exact hp.ne' (enorm_eq_zero.mp hz)
  · rw [measure_range_point] at hm
    exact lt_irrefl _ hm

/-- Ordinary domination of this actual bundle does not imply strong domination. -/
theorem family_not_isStronglyDominated : ¬ family.IsStronglyDominated := by
  intro h
  exact localDist_not_hasIntegrableUpperBound
    (h.localDist referenceFamily_strong
      (S.v_Ωinf_lt_top_of_isRCLike AdelicStructure.normalizedNumberFieldArchimedeanCompletions)).1

/-- Every actual classical full-lattice family is at infinite upper-integral distance. -/
theorem upperIntegralDist_eq_top_of_isClassical (η : NormFamily S Plane) (hη : η.IsClassical) :
    family.upperIntegralDist η = ⊤ := by
  by_contra h
  have hu : HasIntegrableUpperBound (family.localDist η) S.v :=
    hasIntegrableUpperBound_iff_upperEnvelopeIntegral_lt_top.mpr (lt_top_iff_ne_top.mpr h)
  have hc : HasIntegrableUpperBound (η.localDist family) S.v := by
    have he : η.localDist family = family.localDist η := funext fun ω ↦ η.localDist_comm family ω
    rwa [he]
  exact family_not_isStronglyDominated (hη.isStronglyDominated.of_localDist hc)

/-- The actual standard-number-field counterexample to ordinary-domination density in 4.1.36. -/
theorem exists_dominated_infinite_classical_distance :
    ∃ ξ : NormFamily S Plane, ξ.IsDominated ∧ ¬ξ.IsStronglyDominated ∧
      ∀ η : NormFamily S Plane, η.IsClassical → ξ.upperIntegralDist η = ⊤ :=
  ⟨family, family_isDominated, family_not_isStronglyDominated,
    upperIntegralDist_eq_top_of_isClassical⟩

end ArakelovGeometry.NumberFieldResidueDirection

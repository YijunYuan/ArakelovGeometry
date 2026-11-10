/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Index.BoundedElement
public import ArakelovGeometry.NumberTheory.NumberField.Minima.NormFamilyUnitBalancing
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Impurity.Basic
import ArakelovGeometry.AdelicVectorBundle.Minima.BasisSupremum
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Line.Basic
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Line.Index
import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Impurity.Distance
import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Impurity.Minima

/-!
# Actual upper comparison for the integral-basis invariant

The field-only arithmetic constants act on the original number-field
vectors and literal integral lattices. No endpoint finiteness is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldLatticeMinimaUpper

variable (K : Type*) [Field K] [NumberField K]

/-- The actual arithmetic constants depend only on the number field. -/
def comparisonConstant : ℝ :=
  Real.log (NumberFieldBoundedIndex.indexBound K) +
    (Module.finrank ℚ K : ℝ) * NumberFieldUnitBalancing.balancingConstant K

theorem comparisonConstant_nonneg : 0 ≤ comparisonConstant K := by
  have he : (1 : ℝ) ≤ NumberFieldBoundedIndex.indexBound K := by
    exact_mod_cast NumberFieldBoundedIndex.indexBound_pos K
  exact add_nonneg (Real.log_nonneg he)
    (mul_nonneg (Nat.cast_nonneg _) (NumberFieldUnitBalancing.balancingConstant_nonneg K))

end ArakelovGeometry.NumberFieldLatticeMinimaUpper

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

variable (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)

theorem globalImpurity_restrict_eq_zero (hξ : ξ.IsUltrametric)
    (hσ : ξ.globalImpurity = 0) (F : Submodule K E) :
    (ξ.restrict F).globalImpurity = 0 := by
  apply ((ξ.restrict F).globalImpurity_eq_zero_iff_latticeGaugeFamily_eq
    (hξ.restrict F)).mpr
  rw [ξ.latticeGaugeFamily_restrict hξ F,
    (ξ.globalImpurity_eq_zero_iff_latticeGaugeFamily_eq hξ).mp hσ]

omit [FiniteDimensional K E] in
theorem archimedeanMeanLogNorm_restrict (F : Submodule K E) (x : F) :
    (ξ.restrict F).archimedeanMeanLogNorm x = ξ.archimedeanMeanLogNorm (x : E) := by
  rfl

theorem vectorDegree_restrict (hd : ξ.IsDominated) (hm : ξ.IsMeasurable)
    (F : Submodule K E) (x : {x : F // x ≠ 0}) :
    (ξ.restrict F).vectorDegree (hd.restrict F) (hm.restrict F) x =
      ξ.vectorDegree hd hm ⟨x.val.val, fun h => x.property (Subtype.ext h)⟩ := by
  rfl

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NumberFieldLatticeMinimaUpper

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem exists_basis_of_nonzero_line_representatives {ι : Type*}
    (b : Module.Basis ι K E) (x : ι → E)
    (hx : ∀ i, x i ∈ Submodule.span K {b i}) (hne : ∀ i, x i ≠ 0) :
    ∃ c : Module.Basis ι K E, ∀ i, c i = x i := by
  classical
  choose a ha using fun i => Submodule.mem_span_singleton.mp (hx i)
  have ha0 (i) : a i ≠ 0 := by
    intro h
    exact hne i (by simpa [h] using (ha i).symm)
  let c := b.unitsSMul (fun i => Units.mk0 (a i) (ha0 i))
  refine ⟨c, fun i => ?_⟩
  simpa only [c, Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0] using ha i

end ArakelovGeometry.NumberFieldLatticeMinimaUpper

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

variable (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)

theorem vectorDegree_eq_of_mem_span_singleton
    (hd : ξ.IsDominated) (hm : ξ.IsMeasurable)
    (s t : {x : E // x ≠ 0}) (ht : t.val ∈ Submodule.span K {s.val}) :
    ξ.vectorDegree hd hm t = ξ.vectorDegree hd hm s := by
  let : (normalizedNumberFieldAdelicStructure K).IsProper :=
    normalizedNumberFieldAdelicStructure_isProper (K := K)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp ht
  have ha0 : a ≠ 0 := by
    intro h
    exact t.property (by simpa [h] using ha.symm)
  let u : Kˣ := Units.mk0 a ha0
  have he : (⟨(u : K) • s.val, smul_ne_zero u.ne_zero s.property⟩ :
      {x : E // x ≠ 0}) = t := Subtype.ext ha
  simpa only [he] using ξ.vectorDegree_smul_of_proper hd hm u s

/-- Actual arithmetic produces an integral representative of each rational
line and bounds its original infinite-place mean. -/
theorem exists_integral_line_archimedeanMeanLogNorm_bound
    (hξ : ξ.IsUltrametric) (hc : ξ.HasFiniteNormExceptions)
    (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (hσ : ξ.globalImpurity = 0)
    (s : {x : E // x ≠ 0}) :
    ∃ l : E, l ≠ 0 ∧ l ∈ ξ.globalUnitBall ∧ l ∈ Submodule.span K {s.val} ∧
      (Module.finrank ℚ K : ℝ) * ξ.archimedeanMeanLogNorm l ≤
        Real.log (NumberFieldBoundedIndex.indexBound K) - ξ.vectorDegree hd hm s := by
  classical
  let F := Submodule.span K {s.val}
  have hr : Module.finrank K F = 1 := finrank_span_singleton s.property
  obtain ⟨l, hl, hquot, hcard⟩ :=
    ξ.exists_normalizedLineGlobalUnitBall_boundedIndex_element hξ hc hd F hr
  have hlF : l.val ≠ 0 := fun h => hl (Subtype.ext h)
  have hlE : (l.val : E) ≠ 0 := fun h => hlF (Subtype.ext h)
  have hdeg := (ξ.restrict F).normalizedLineGlobalUnitBall_vectorDegree
    (hξ.restrict F) (hc.restrict F) (hd.restrict F) (hm.restrict F)
    (ξ.globalImpurity_restrict_eq_zero hξ hσ F) hr l hl
  rw [← (ξ.restrict F).degree_mul_archimedeanMeanLogNorm_eq_integral,
    ξ.archimedeanMeanLogNorm_restrict,
    ξ.vectorDegree_restrict hd hm F] at hdeg
  have heq := ξ.vectorDegree_eq_of_mem_span_singleton hd hm s
    ⟨(l.val : E), hlE⟩ l.val.property
  rw [heq] at hdeg
  let := hquot
  have hpos : 0 < Nat.card
      (((ξ.restrict F).globalUnitBallModule (hξ.restrict F)) ⧸
        Submodule.span (𝓞 K) {l}) := Nat.card_pos
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hpos)
    (show (Nat.card (((ξ.restrict F).globalUnitBallModule (hξ.restrict F)) ⧸
      Submodule.span (𝓞 K) {l}) : ℝ) ≤ NumberFieldBoundedIndex.indexBound K by
        exact_mod_cast hcard)
  refine ⟨(l.val : E), hlE, l.property, l.val.property, ?_⟩
  linarith

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Every actual high-degree basis produces an actual integral-basis threshold
through bounded-index line representatives and Dirichlet units. -/
theorem mem_integralBasisThresholds_of_vectorDegree_basis
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsUltrametric) (hc : ξ.HasFiniteNormExceptions)
    (hd : ξ.IsDominated) (hm : ξ.IsMeasurable) (hσ : ξ.globalImpurity = 0)
    (b : Module.Basis (Fin (Module.finrank K E)) K E) {t : ℝ}
    (ht : ∀ i, t ≤ ξ.vectorDegree hd hm ⟨b i, b.ne_zero i⟩) :
    (t - NumberFieldLatticeMinimaUpper.comparisonConstant K) /
      (Module.finrank ℚ K : ℝ) ∈ ξ.integralBasisThresholds := by
  classical
  choose l hl hball hline hmean using fun i =>
    ξ.exists_integral_line_archimedeanMeanLogNorm_bound hξ hc hd hm hσ ⟨b i, b.ne_zero i⟩
  obtain ⟨c, hc⟩ := NumberFieldLatticeMinimaUpper.exists_basis_of_nonzero_line_representatives
    b l hline hl
  apply ξ.mem_integralBasisThresholds_of_archimedeanMeanLogNorm_le c
    (fun i => by rw [hc i]; exact hball i)
  intro i
  rw [hc i]
  have hdpos : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  rw [show -((t - NumberFieldLatticeMinimaUpper.comparisonConstant K) /
      (Module.finrank ℚ K : ℝ)) =
      (NumberFieldLatticeMinimaUpper.comparisonConstant K - t) /
        (Module.finrank ℚ K : ℝ) by ring]
  apply (le_div_iff₀ hdpos).mpr
  dsimp [NumberFieldLatticeMinimaUpper.comparisonConstant]
  have hi := hmean i
  have hti := ht i
  nlinarith

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

open AdelicStructure NormFamily

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The pure case of source Proposition4.4.10, without finite-endpoint or
attainment hypotheses and including the empty basis convention. -/
theorem minimalLogarithmicMinimum_le_degree_mul_latticeLambda_add_constant_of_impurity_zero
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hV : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions)
    (hσ : V.toNormFamily.globalImpurity = 0) :
    V.minimalLogarithmicMinimum ≤
      ((Module.finrank ℚ K : ℝ) : EReal) * V.toNormFamily.latticeLambda +
        (NumberFieldLatticeMinimaUpper.comparisonConstant K : EReal) := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨b, hb⟩ := (V.finrank_le_degreeThresholdSpan_iff_exists_basis t).mp ht
  have ha := V.toNormFamily.mem_integralBasisThresholds_of_vectorDegree_basis
    hV hc V.isDominated V.isMeasurable hσ b hb
  have hlambda : (((t - NumberFieldLatticeMinimaUpper.comparisonConstant K) /
      (Module.finrank ℚ K : ℝ) : ℝ) : EReal) ≤ V.toNormFamily.latticeLambda :=
    le_iSup_of_le _ (le_iSup_of_le ha le_rfl)
  have hdpos : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  have he : (Module.finrank ℚ K : ℝ) *
      ((t - NumberFieldLatticeMinimaUpper.comparisonConstant K) /
        (Module.finrank ℚ K : ℝ)) + NumberFieldLatticeMinimaUpper.comparisonConstant K = t := by
    field_simp
    ring
  calc
    (t : EReal) = ((Module.finrank ℚ K : ℝ) : EReal) *
        (((t - NumberFieldLatticeMinimaUpper.comparisonConstant K) /
          (Module.finrank ℚ K : ℝ) : ℝ) : EReal) +
          (NumberFieldLatticeMinimaUpper.comparisonConstant K : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_add, he]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hlambda
      (EReal.coe_nonneg.mpr hdpos.le)) le_rfl

end ArakelovGeometry.AdelicVectorBundle

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Literal finite unit-ball equality transfers genuine source coherence. -/
theorem HasFiniteNormExceptions.latticeGaugeFamily
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hc : ξ.HasFiniteNormExceptions) (hξ : ξ.IsUltrametric) :
    (ξ.latticeGaugeFamily hξ).HasFiniteNormExceptions := by
  intro x
  apply (hc x).subset
  intro ω hω
  obtain ⟨hfin, hgt⟩ := hω
  refine ⟨hfin, ?_⟩
  apply lt_of_not_ge
  intro hle
  have hg : (ξ.latticeGaugeFamily hξ).norm ω (1 ⊗ₜ[K] x) ≤ 1 := by
    change (1 ⊗ₜ[K] x) ∈ (ξ.latticeGaugeFamily hξ).completedUnitBall ω
    rw [ξ.latticeGaugeFamily_completedUnitBall_eq hξ ω hfin]
    exact hle
  exact (not_le_of_gt hgt) hg

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

open AdelicStructure NormFamily

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The full actual upper comparison of source Proposition4.4.10. The
impurity term is the literal source impurity, proved finite by domination
and coherence, and evaluated in the real line. -/
theorem minimalLogarithmicMinimum_le_degree_mul_latticeLambda_add_impurity_add_constant
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hV : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions) :
    V.minimalLogarithmicMinimum ≤
      ((Module.finrank ℚ K : ℝ) : EReal) * V.toNormFamily.latticeLambda +
        (V.toNormFamily.globalImpurity.toReal : EReal) +
        (NumberFieldLatticeMinimaUpper.comparisonConstant K : EReal) := by
  have hp := minimalLogarithmicMinimum_le_degree_mul_latticeLambda_add_constant_of_impurity_zero
    (V.numberFieldLatticeGauge hV hc)
      (V.toNormFamily.latticeGaugeFamily_isUltrametric hV) (hc.latticeGaugeFamily hV)
      (V.numberFieldLatticeGauge_globalImpurity_eq_zero hV hc)
  rw [V.numberFieldLatticeGauge_latticeLambda_eq hV hc] at hp
  have h := (V.logarithmicMinimum_le_numberFieldLatticeGauge_add_globalImpurity
    hV hc (Module.finrank K E)).trans (add_le_add hp le_rfl)
  simpa only [minimalLogarithmicMinimum, add_assoc, add_comm, add_left_comm] using h

end ArakelovGeometry.AdelicVectorBundle

namespace ArakelovGeometry.AdelicVectorBundle

open AdelicStructure NormFamily

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- Source Proposition4.4.10 for the actual normalized number-field bundle,
with a field-only constant and the literal integral invariant and impurity. -/
theorem numberField_latticeLambda_logarithmicMinimum_comparison
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hV : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions) :
    ((Module.finrank ℚ K : ℝ) : EReal) * V.toNormFamily.latticeLambda ≤
        V.minimalLogarithmicMinimum ∧
      V.minimalLogarithmicMinimum ≤
        ((Module.finrank ℚ K : ℝ) : EReal) * V.toNormFamily.latticeLambda +
          (V.toNormFamily.globalImpurity.toReal : EReal) +
          (NumberFieldLatticeMinimaUpper.comparisonConstant K : EReal) :=
  ⟨V.degree_mul_latticeLambda_le_minimalLogarithmicMinimum,
    V.minimalLogarithmicMinimum_le_degree_mul_latticeLambda_add_impurity_add_constant hV hc⟩

end ArakelovGeometry.AdelicVectorBundle

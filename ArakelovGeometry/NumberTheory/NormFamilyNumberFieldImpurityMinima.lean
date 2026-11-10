/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldLatticeGaugeDomination
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldLatticeLambda
import ArakelovGeometry.AdelicVectorBundle.LogarithmicMinimaBasisSupremum

/-!
# Actual impurity control of logarithmic minima

The canonical gauge replacement is an actual dominated adelic bundle under
source coherence. It preserves the literal integral-basis invariant and
removes impurity. The actual integrated distance bounds vector degrees and
ordinary minima with the explicit impurity cost.
-/

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

variable {K E : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual integrated fibre distance bounds the difference of vector degrees. -/
theorem vectorDegree_le_add_integral_localDist
    (ξ η : NormFamily S E) (hdξ : ξ.IsDominated) (hmξ : ξ.IsMeasurable)
    (hdη : η.IsDominated) (hmη : η.IsMeasurable)
    (hδ : Integrable (ξ.localDist η) S.v) (x : {x : E // x ≠ 0}) :
    ξ.vectorDegree hdξ hmξ x ≤ η.vectorDegree hdη hmη x +
      ∫ ω, ξ.localDist η ω ∂S.v := by
  have hξ := hdξ.integrable_logNorm hmξ x.val
  have hη := hdη.integrable_logNorm hmη x.val
  have hpoint (ω : S.Ω) : η.logNorm x.val ω - ξ.logNorm x.val ω ≤ ξ.localDist η ω := by
    have h := (abs_le.mp (ξ.log_norm_sub_le_localDist η ω (1 ⊗ₜ[K] x.val))).1
    change -ξ.localDist η ω ≤ ξ.logNorm x.val ω - η.logNorm x.val ω at h
    linarith
  have hi := integral_mono (hη.sub hξ) hδ hpoint
  change (∫ ω, η.logNorm x.val ω - ξ.logNorm x.val ω ∂S.v) ≤ _ at hi
  rw [integral_sub hη hξ] at hi
  rw [ξ.vectorDegree_eq_neg_integral hdξ hmξ x, η.vectorDegree_eq_neg_integral hdη hmη x]
  linarith

variable [NumberField K]

open AdelicStructure

/-- The actual real distance integral equals the finite source impurity. -/
theorem integral_localDist_latticeGaugeFamily_eq_globalImpurity_toReal
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (hξ : ξ.IsUltrametric)
    (hσ : ξ.globalImpurity ≠ ⊤) :
    (∫ ω, ξ.localDist (ξ.latticeGaugeFamily hξ) ω
      ∂(normalizedNumberFieldAdelicStructure K).v) = ξ.globalImpurity.toReal := by
  rw [ξ.globalImpurity_eq_lintegral_localDist_latticeGaugeFamily hξ]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (ξ.localDist_nonneg (ξ.latticeGaugeFamily hξ)))
    ((ξ.globalImpurity_ne_top_iff_integrable_localDist_latticeGaugeFamily hξ).mp
      hσ).aestronglyMeasurable

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

variable {K E : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Ordinary logarithmic minima change by at most the actual distance integral,
including the auxiliary zero and above-rank indices. -/
theorem logarithmicMinimum_le_add_integral_localDist
    (V W : AdelicVectorBundle S E)
    (hδ : Integrable (V.toNormFamily.localDist W.toNormFamily) S.v) (i : ℕ) :
    V.logarithmicMinimum i ≤ W.logarithmicMinimum i +
      ((∫ ω, V.toNormFamily.localDist W.toNormFamily ω ∂S.v : ℝ) : EReal) := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨x, hli, hx⟩ := (V.le_finrank_degreeThresholdSpan_iff i t).mp ht
  let D : ℝ := ∫ ω, V.toNormFamily.localDist W.toNormFamily ω ∂S.v
  have hb : ((t - D : ℝ) : EReal) ≤ W.logarithmicMinimum i := by
    apply W.coe_le_logarithmicMinimum_of_linearIndependent x hli
    intro j
    have h := V.toNormFamily.vectorDegree_le_add_integral_localDist W.toNormFamily
      V.isDominated V.isMeasurable W.isDominated W.isMeasurable hδ (x j)
    change V.vectorDegree (x j) ≤ W.vectorDegree (x j) + D at h
    linarith [hx j]
  have h := add_le_add_right hb (D : EReal)
  have he : (D : EReal) + ((t - D : ℝ) : EReal) = (t : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    ring
  rw [he, add_comm] at h
  exact h

variable [NumberField K]

open AdelicStructure NormFamily

/-- The genuine source gauge replacement, with actual regularity produced
from discrete measurability and coherent lattice domination. -/
def numberFieldLatticeGauge
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hV : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions) :
    AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E := by
  let hd := hc.latticeGaugeFamily_isDominated V.toNormFamily hV
    (V.isDominated.fg_normalizedGlobalUnitBallModule hV)
  let : DiscreteMeasurableSpace (normalizedNumberFieldAdelicStructure K).Ω :=
    inferInstanceAs (DiscreteMeasurableSpace
      {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K})
  exact ofMeasurableDominated (V.toNormFamily.latticeGaugeFamily hV)
    (V.toNormFamily.latticeGaugeFamily hV).isMeasurable_of_discrete hd (Or.inl inferInstance)

@[simp]
theorem numberFieldLatticeGauge_toNormFamily
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hV : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions) :
    (V.numberFieldLatticeGauge hV hc).toNormFamily = V.toNormFamily.latticeGaugeFamily hV := rfl

theorem numberFieldLatticeGauge_globalImpurity_eq_zero
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hV : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions) :
    (V.numberFieldLatticeGauge hV hc).toNormFamily.globalImpurity = 0 :=
  V.toNormFamily.latticeGaugeFamily_globalImpurity_eq_zero hV

theorem numberFieldLatticeGauge_latticeLambda_eq
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hV : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions) :
    (V.numberFieldLatticeGauge hV hc).toNormFamily.latticeLambda = V.toNormFamily.latticeLambda :=
  V.toNormFamily.latticeGaugeFamily_latticeLambda_eq hV

/-- The original ordinary minimum is bounded by the produced gauge minimum
plus the literal source impurity, with no zero-cost transfer asserted. -/
theorem logarithmicMinimum_le_numberFieldLatticeGauge_add_globalImpurity
    (V : AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) E)
    (hV : V.toNormFamily.IsUltrametric) (hc : V.toNormFamily.HasFiniteNormExceptions) (i : ℕ) :
    V.logarithmicMinimum i ≤ (V.numberFieldLatticeGauge hV hc).logarithmicMinimum i +
      (V.toNormFamily.globalImpurity.toReal : EReal) := by
  have hσ := V.isDominated.globalImpurity_ne_top V.toNormFamily hV hc
  have hδ :=
    (V.toNormFamily.globalImpurity_ne_top_iff_integrable_localDist_latticeGaugeFamily hV).mp hσ
  have h := V.logarithmicMinimum_le_add_integral_localDist (V.numberFieldLatticeGauge hV hc) hδ i
  rw [numberFieldLatticeGauge_toNormFamily,
    V.toNormFamily.integral_localDist_latticeGaugeFamily_eq_globalImpurity_toReal hV hσ] at h
  exact h

end ArakelovGeometry.AdelicVectorBundle

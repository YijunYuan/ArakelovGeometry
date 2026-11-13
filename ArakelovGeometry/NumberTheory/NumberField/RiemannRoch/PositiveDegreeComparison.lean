/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Positive.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Model.Sections
public import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.ComparisonConstants

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.ComparisonConstantMonotone
import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.NonnegativeSlopeCount
import ArakelovGeometry.NumberTheory.NumberField.RiemannRoch.RestrictionModel
import Mathlib.Topology.Sheaves.Init

/-! # Classical arithmetic h0 and positive degree: Chen–Moriwaki 4.3.24 -/

@[expose] public section

noncomputable section
open NumberField
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldClassicalPositiveDegreeComparison

open AdelicStructure NumberFieldProjectiveGeneric NumberFieldFullLattice
  NumberFieldClassicalComparisonConstants NumberFieldClassicalComparisonConstantMonotone
  NumberFieldClassicalNonnegativeSlopeCount NumberFieldClassicalRestrictionModel
open NumberFieldInvertibleGeneric (genericImage genericImage_fullSpan)

universe u
variable {K : Type u} [Field K] [NumberField K]
  (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Chen–Moriwaki4.3.24 for an actual finite projective Hermitian arithmetic
module, with the exact printed factorial constant. The positive degree is
finite: the actual HN arithmetic model identifies it with a real degree. -/
theorem abs_logSectionCount_sub_positiveDegree_le
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M))
    [hη : η.IsHermitian] :
    let V := fullLatticeAdelicBundle (genericImage (K := K) M)
      (genericImage_fg M) (genericImage_fullSpan M) η
    |logSectionCount M η - (V.positiveDegree
     ).toReal| ≤
        (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * Real.log |(NumberField.discr K : ℝ)| +
          comparisonConstant K (Module.finrank K (K ⊗[𝓞 K] M)) := by
  let L := genericImage (K := K) M
  let hfg := genericImage_fg (K := K) M
  let hspan := genericImage_fullSpan (K := K) M
  let V := fullLatticeAdelicBundle L hfg hspan η
  let hV := fullLatticeGaugeFamily_isHermitian L hfg hspan η
  let F := V.hermitianHNFiltration
    (hV := hV) 0
  let W := V.restrictOfNormMeasurability F
  let hW := hV.restrict F
  let hpW := (fullLatticeGaugeFamily_isPureAtFinitePlaces L hfg hspan η).restrict F
  let A := W.toNormFamily.globalUnitBallModule (hξ := hW.1)
  let ζ := integralModelFamily W (hV := hW) (hpure := hpW)
  let := integralModel_finite W (hV := hW) (hpure := hpW)
  let := integralModel_projective W (hV := hW) (hpure := hpW)
  let B := fullLatticeAdelicBundle (genericImage (K := K) A)
    (genericImage_fg A) (genericImage_fullSpan A) ζ
  have hmodel := original_hnZero_arithmetic_model M η
  have hζ := integralModelFamily_isHermitian W (hV := hW) (hpure := hpW)
  have hA := abs_logSectionCount_sub_degree_le_rank_log_discr A ζ (hη := hζ) hmodel.2.2.1
  have hpd : V.positiveDegree
      =
        (B.degree : EReal) :=
    hmodel.2.1
  change |logSectionCount M η - (V.positiveDegree
   ).toReal| ≤ _
  rw [hpd, EReal.toReal_coe, hmodel.1]
  exact hA.trans (rank_error_monotone K hmodel.2.2.2)

end ArakelovGeometry.NumberFieldClassicalPositiveDegreeComparison

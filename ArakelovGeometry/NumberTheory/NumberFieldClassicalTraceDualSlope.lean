/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.LineVectorDegree
public import ArakelovGeometry.AdelicVectorBundle.SlopesDualUpper
public import ArakelovGeometry.AdelicVectorBundle.SlopesRescaling
public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldPureDuality
public import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldPureModel
public import ArakelovGeometry.NumberTheory.NumberFieldClassicalTraceDualMetric
public import ArakelovGeometry.NumberTheory.NumberFieldClassicalTraceDualPurity
public import ArakelovGeometry.NumberTheory.NumberFieldTraceDualizingLineCovolume

/-! # Extremal slopes of the original prescribed arithmetic trace dual -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldClassicalTraceDualSlope

universe u v

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Exact Hermitian extremal duality, including the zero-space conventions. -/
theorem maximalSlope_dual_eq_neg_minimalSlope
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.IsHermitian hN) :
    (V.dualOfMeasurableBase hS).maximalSlope hS hN = -V.minimalSlope hS hN := by
  by_cases hr : Module.finrank K E = 0
  · rw [(V.dualOfMeasurableBase hS).maximalSlope_eq_bot_of_finrank_eq_zero hS hN
      (Subspace.dual_finrank_eq.trans hr), V.minimalSlope_eq_top_of_finrank_eq_zero hS hN hr]
    rfl
  have hrpos : 0 < Module.finrank K E := Nat.pos_of_ne_zero hr
  let D := V.dualOfMeasurableBase hS
  have hrD : 0 < Module.finrank K (Module.Dual K E) := by
    rwa [Subspace.dual_finrank_eq]
  have hbidual : (D.dualOfMeasurableBase hS).minimalSlope hS hN =
      V.minimalSlope hS hN := by
    symm
    apply V.minimalSlope_eq_of_completed_isometry _ (Module.evalEquiv K E) hS hN
    intro ω z
    simp only [AdelicVectorBundle.dualOfMeasurableBase_toNormFamily,
      Module.evalEquiv_toLinearMap]
    by_cases hω : ω ∈ S.Ωfin
    · exact hV.1.dual_dual_norm_eval ω hω z
    · exact V.toNormFamily.dual_dual_norm_eval_eq_of_isRCLike ω (hN ω hω) z
  have he := D.minimalSlope_dual_add_maximalSlope_eq_zero_of_isHermitian
    hS hN hV.dual hrD
  rw [hbidual] at he
  obtain ⟨a, ha⟩ := V.exists_minimalSlope_eq_coe hS hN hrpos
  obtain ⟨b, hb⟩ := D.exists_maximalSlope_eq_coe hS hN hrD
  rw [ha, hb, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_eq_coe_iff] at he
  change D.maximalSlope hS hN = -V.minimalSlope hS hN
  rw [ha, hb, ← EReal.coe_neg]
  exact congrArg (fun t : ℝ => (t : EReal)) (by linarith : b = -a)

/-- Tensoring with an actual scalar line shifts maximal slope by its degree. -/
theorem maximalSlope_orthogonalTensor_scalarLine
    (V : AdelicVectorBundle S E) (L : AdelicVectorBundle S K)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.IsHermitian hN) (hL : L.IsHermitian hN) :
    (V.orthogonalTensorPair L hS hN hV hL).maximalSlope hS hN =
      V.maximalSlope hS hN + (L.degree hS hN : EReal) := by
  let φ := L.toNormFamily.logNorm (1 : K)
  let hm := L.isMeasurable.logNorm (1 : K)
  let hi := L.integrable_logNorm (1 : K)
  let R := V.scaleExp φ hm hi
  let P := V.orthogonalTensorPair L hS hN hV hL
  have he : R.maximalSlope hS hN = P.maximalSlope hS hN := by
    apply R.maximalSlope_eq_of_completed_isometry P (TensorProduct.rid K E).symm hS hN
    intro ω z
    change (V.toNormFamily.orthogonalTensorPair L.toNormFamily hN hV hL).norm ω
        (LinearEquiv.baseChange K (S.ϕ ω).Completion _ _ (TensorProduct.rid K E).symm z) =
      Real.exp (φ ω) * V.norm ω z
    rw [NumberFieldProjectiveTraceDualMetric.tensorUnitBaseChange_symm]
    erw [NormFamily.orthogonalTensorPair_norm_tmul_completed]
    change _ = Real.exp (Real.log (L.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (1 : K)))) * _
    rw [Real.exp_log (L.toNormFamily.norm_rational_pos ω one_ne_zero), mul_comm]
  have hdeg : L.degree hS hN = -(∫ ω, φ ω ∂S.v) := by
    rw [L.degree_eq_lineDegree hS hN (Module.finrank_self K),
      L.lineDegree_eq_neg_integral (Module.finrank_self K) ⟨1, one_ne_zero⟩]
  rw [← he, V.maximalSlope_scaleExp φ hm hi hS hN, hdeg, EReal.coe_neg]
  rfl

/-- Scalar-valued base change is the completed dual evaluation times the scalar unit. -/
theorem baseChange_functional_eq_tmul (F : Type*) [Field F] [Algebra K F]
    (f : Module.Dual K E) (x : F ⊗[K] E) :
    LinearMap.baseChange F f x =
      (dualBaseChangeEquiv K F E ((1 : F) ⊗ₜ[K] f) x) ⊗ₜ[K] (1 : K) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy, TensorProduct.add_tmul]
  | tmul a x =>
    simp only [LinearMap.baseChange_tmul, dualBaseChangeEquiv_tmul_apply_tmul, one_mul]
    simpa only [smul_eq_mul, mul_one, one_mul, Algebra.smul_def, mul_comm] using
      (TensorProduct.smul_tmul (R := K) (f x) a (1 : K)).symm

section NumberField

open AdelicStructure
variable [NumberField K]
attribute [local instance] NumberFieldFullLattice.degreeCovolumeDiscrete
local notation "curve" => normalizedNumberFieldAdelicStructure K

/-- At a pure finite place, the scalar-line scaled dual ball is the literal
ball of maps into that scalar line's completed unit ball. -/
theorem scalarLine_mul_dual_norm_le_one_iff
    (ξ : NormFamily (curve) E) (L : NormFamily (curve) K)
    (hξ : ξ.IsPureAtFinitePlaces) (hL : L.IsPureAtFinitePlaces)
    (ω : (curve).Ω) (hω : ω ∈ (curve).Ωfin)
    (f : Module.Dual K E) :
    L.norm ω ((1 : ((curve).ϕ ω).Completion) ⊗ₜ[K] (1 : K)) *
        ξ.dual.norm ω ((1 : ((curve).ϕ ω).Completion) ⊗ₜ[K] f) ≤ 1 ↔
      ∀ x, ξ.norm ω x ≤ 1 → L.norm ω (LinearMap.baseChange _ f x) ≤ 1 := by
  let F := ((curve).ϕ ω).Completion
  have hone : ((1 : F) ⊗ₜ[K] (1 : K)) ≠ 0 := by
    intro h
    have hh := congrArg (TensorProduct.AlgebraTensorModule.rid K F F) h
    simp at hh
  obtain ⟨b, hb, hbn⟩ := hL ω hω _ hone
  have he (x : F ⊗[K] E) :
      L.norm ω (LinearMap.baseChange F f x) =
        L.norm ω ((1 : F) ⊗ₜ[K] (1 : K)) *
          ‖dualBaseChangeEquiv K F E ((1 : F) ⊗ₜ[K] f) x‖ := by
    rw [baseChange_functional_eq_tmul]
    have ht (c : F) : c ⊗ₜ[K] (1 : K) = c • ((1 : F) ⊗ₜ[K] (1 : K)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, L.norm_smul, mul_comm]
  have hd := hξ.dual_norm_le_one_iff_unitBall ω hω (b • ((1 : F) ⊗ₜ[K] f))
  rw [ξ.dual.norm_smul, ← hbn] at hd
  simp only [dualBaseChangeEquiv_smul, LinearMap.smul_apply, norm_smul, ← hbn] at hd
  constructor
  · intro h x hx
    rw [he x]
    exact hd.mp h x hx
  · intro h
    apply hd.mpr
    intro x hx
    rw [← he x]
    exact h x hx

open NumberFieldFullLattice NumberFieldTraceDualizingLine NumberFieldCodifferentDual

/-- The finite global scaled-dual unit ball consists of the actual maps from
an originally prescribed full lattice into the actual codifferent. -/
theorem fullLattice_scaledDual_ball_iff_codifferent
    (L : Submodule (NumberField.RingOfIntegers K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤)
    (η : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (f : Module.Dual K E) :
    (∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin,
      (dualizingLine K).norm ω
          ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion) ⊗ₜ[K] (1 : K)) *
        (fullLatticeGaugeFamily L hfg hspan η).dual.norm ω
          ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion) ⊗ₜ[K] f) ≤ 1) ↔
      ∀ m : L, f (m : E) ∈ codifferentModule K := by
  let ξ := fullLatticeGaugeFamily L hfg hspan η
  let Q := (dualizingLine K).toNormFamily
  have hp := fullLatticeGaugeFamily_isPureAtFinitePlaces L hfg hspan η
  have hQp := dualizingLine_isPureAtFinitePlaces K
  have hQu := (dualizingLine_isHermitian K).1
  constructor
  · intro hf m
    change f (m : E) ∈ (codifferentModule K : Set K)
    rw [← dualizingLine_globalUnitBall_eq K]
    intro ω hω
    have hm : (m : E) ∈ ξ.globalUnitBall := by
      rw [fullLatticeGaugeFamily_globalUnitBall_eq L hfg hspan η]
      exact m.property
    have h := (scalarLine_mul_dual_norm_le_one_iff ξ Q hp hQp ω hω f).mp
      (hf ω hω) (1 ⊗ₜ[K] (m : E)) (hm ω hω)
    rwa [LinearMap.baseChange_tmul] at h
  · intro hf ω hω
    apply (scalarLine_mul_dual_norm_le_one_iff ξ Q hp hQp ω hω f).mpr
    obtain ⟨p, rfl⟩ := ActualPrimeIndexing.exists_normalizedPrimeParameter_eq ω hω
    let ω := ActualPrimeIndexing.normalizedPrimeParameter p
    let F := ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion
    let O := (normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω
    let B := Q.completedUnitBallModule ω hω hQu
    have hle : NumberFieldModel.completedLatticeSpan L p ≤
        B.comap ((LinearMap.baseChange F f).restrictScalars O) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨m, rfl⟩
      change Q.norm ω (LinearMap.baseChange F f ((1 : F) ⊗ₜ[K] (m : E))) ≤ 1
      rw [LinearMap.baseChange_tmul]
      have hm : f (m : E) ∈ Q.globalUnitBall := by
        rw [dualizingLine_globalUnitBall_eq K]
        exact hf m
      exact hm ω hω
    intro z hz
    have hzL : z ∈ NumberFieldModel.completedLatticeSpan L p := by
      change z ∈ (NumberFieldModel.completedLatticeSpan L p : Set _)
      rw [← fullLatticeGaugeFamily_completedUnitBall_eq L hfg hspan η p]
      exact hz
    exact hle hzL

open NumberFieldProjectiveGeneric NumberFieldProjectiveTraceDual
  NumberFieldProjectiveTraceDualGeneric NumberFieldProjectiveTraceDualMetric
  NumberFieldClassicalTraceDual NumberFieldClassicalTraceDualMetric
  NumberFieldIntegralTraceDual
open NumberFieldInvertibleGeneric (genericImage genericImage_fullSpan)

attribute [local instance] genericFiniteDimensional traceTensor_finite traceTensor_projective

variable (M : Type u) [AddCommGroup M] [Module (NumberField.RingOfIntegers K) M]
  [Module.Finite (NumberField.RingOfIntegers K) M]
  [Module.Projective (NumberField.RingOfIntegers K) M]

/-- The prescribed original trace-dual tensor has exactly its literal
original generic lattice as its finite global unit ball. -/
theorem originalPrescribedTraceDualFamily_globalUnitBallModule
    (η : NormFamily (normalizedNumberFieldAdelicStructure K)
      (K ⊗[NumberField.RingOfIntegers K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    let L := genericImage (K := K) M
    let ξ := fullLatticeGaugeFamily L (genericImage_fg M) (genericImage_fullSpan M) η
    let hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions :=
      fullLatticeGaugeFamily_isHermitian L (genericImage_fg M) (genericImage_fullSpan M) η hη
    (originalPrescribedTraceDualFamily M hξ).globalUnitBallModule
      (originalPrescribedTraceDualFamily_isHermitian M hξ).1 =
      genericImage (K := K) (codifferentModule K ⊗[NumberField.RingOfIntegers K]
        Module.Dual (NumberField.RingOfIntegers K) M) := by
  let L := genericImage (K := K) M
  let ξ := fullLatticeGaugeFamily L (genericImage_fg M) (genericImage_fullSpan M) η
  let hξ := fullLatticeGaugeFamily_isHermitian L (genericImage_fg M)
    (genericImage_fullSpan M) η hη
  let δ := originalPrescribedTraceDualFamily M hξ
  let e := (traceTensorGenericPairEquiv (K := K) M).trans
    (TensorProduct.rid K (Module.Dual K (K ⊗[NumberField.RingOfIntegers K] M)))
  have he (z : codifferentModule K ⊗[NumberField.RingOfIntegers K]
      Module.Dual (NumberField.RingOfIntegers K) M) :
      e ((1 : K) ⊗ₜ[NumberField.RingOfIntegers K] z) =
        traceTensorInclusion (K := K) M z := by
    exact (traceTensorGenericPairEquiv_contract M 1 z).trans (one_smul K _)
  have hn (ω : (normalizedNumberFieldAdelicStructure K).Ω)
      (x : K ⊗[NumberField.RingOfIntegers K]
        (codifferentModule K ⊗[NumberField.RingOfIntegers K]
          Module.Dual (NumberField.RingOfIntegers K) M)) :
      δ.norm ω ((1 : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion) ⊗ₜ[K] x) =
        (dualizingLine K).norm ω (1 ⊗ₜ[K] (1 : K)) *
          ξ.dual.norm ω (1 ⊗ₜ[K] e x) := by
    let F := ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion
    let r := TensorProduct.rid K (Module.Dual K (K ⊗[NumberField.RingOfIntegers K] M))
    have hx : traceTensorGenericPairEquiv M x = r.symm (e x) := by
      exact (r.symm_apply_apply _).symm
    change (prescribedTraceDualFamily hξ).norm ω
      ((1 : F) ⊗ₜ[K] traceTensorGenericPairEquiv M x) = _
    rw [hx]
    change (prescribedTraceDualFamily hξ).norm ω
      (LinearEquiv.baseChange K F _ _ r.symm ((1 : F) ⊗ₜ[K] e x)) = _
    rw [tensorUnitBaseChange_symm]
    erw [NormFamily.orthogonalTensorPair_norm_tmul_completed]
    exact mul_comm _ _
  have hm (x : K ⊗[NumberField.RingOfIntegers K]
      (codifferentModule K ⊗[NumberField.RingOfIntegers K]
        Module.Dual (NumberField.RingOfIntegers K) M)) :
      x ∈ δ.globalUnitBall ↔ e x ∈ integralTraceDual L := by
    change (∀ ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin,
      δ.norm ω (1 ⊗ₜ[K] x) ≤ 1) ↔ _
    simp_rw [hn]
    exact (fullLattice_scaledDual_ball_iff_codifferent L (genericImage_fg M)
      (genericImage_fullSpan M) η (e x)).trans
        (mem_integralTraceDual_iff_codifferent L (e x)).symm
  ext x
  constructor
  · intro hx
    have hf := (hm x).mp hx
    rw [← traceTensorInclusion_range M] at hf
    obtain ⟨z, hz⟩ := hf
    refine ⟨z, ?_⟩
    apply e.injective
    exact (he z).trans hz
  · rintro ⟨z, rfl⟩
    apply (hm _).mpr
    erw [he, ← traceTensorInclusion_range M]
    exact ⟨z, rfl⟩

/-- Domination of the prescribed trace dual is produced from the actual
full-lattice bundle, its actual dual, and the actual dualizing line. -/
theorem originalPrescribedTraceDualFamily_isDominated
    (η : NormFamily (normalizedNumberFieldAdelicStructure K)
      (K ⊗[NumberField.RingOfIntegers K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    let L := genericImage (K := K) M
    let ξ := fullLatticeGaugeFamily L (genericImage_fg M) (genericImage_fullSpan M) η
    let hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions :=
      fullLatticeGaugeFamily_isHermitian L (genericImage_fg M) (genericImage_fullSpan M) η hη
    (originalPrescribedTraceDualFamily M hξ).IsDominated := by
  let L := genericImage (K := K) M
  let V := fullLatticeAdelicBundle L (genericImage_fg M) (genericImage_fullSpan M) η
  let hV := fullLatticeGaugeFamily_isHermitian L (genericImage_fg M)
    (genericImage_fullSpan M) η hη
  let D := V.dualOfMeasurableBase (Or.inl inferInstance)
  have hd := D.isDominated.strong_orthogonalTensorPair (dualizingLine K).isDominated
    normalizedNumberFieldArchimedeanCompletions hV.dual (dualizingLine_isHermitian K)
  exact hd.isDominated.pullback (traceTensorGenericPairEquiv M).toLinearMap
    (traceTensorGenericPairEquiv M).injective

set_option backward.isDefEq.respectTransparency false in
/-- The actual original full-lattice gauges recover the prescribed trace-dual
family at every completed place. -/
theorem originalPrescribedTraceDualFamily_eq_fullLatticeGaugeFamily
    (η : NormFamily (normalizedNumberFieldAdelicStructure K)
      (K ⊗[NumberField.RingOfIntegers K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    let L := genericImage (K := K) M
    let ξ := fullLatticeGaugeFamily L (genericImage_fg M) (genericImage_fullSpan M) η
    let hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions :=
      fullLatticeGaugeFamily_isHermitian L (genericImage_fg M) (genericImage_fullSpan M) η hη
    let T := codifferentModule K ⊗[NumberField.RingOfIntegers K]
      Module.Dual (NumberField.RingOfIntegers K) M
    let δ := originalPrescribedTraceDualFamily M hξ
    fullLatticeGaugeFamily (genericImage (K := K) T) (genericImage_fg T)
      (genericImage_fullSpan T) δ = δ := by
  let L := genericImage (K := K) M
  let ξ := fullLatticeGaugeFamily L (genericImage_fg M) (genericImage_fullSpan M) η
  let hξ := fullLatticeGaugeFamily_isHermitian L (genericImage_fg M)
    (genericImage_fullSpan M) η hη
  let δ := originalPrescribedTraceDualFamily M hξ
  have hd : δ.IsDominated := originalPrescribedTraceDualFamily_isDominated M η hη
  have hp : δ.IsPureAtFinitePlaces :=
    NumberFieldClassicalTraceDualPurity.originalPrescribedTraceDualFamily_isPureAtFinitePlaces
      M hξ (fullLatticeGaugeFamily_isPureAtFinitePlaces L (genericImage_fg M)
        (genericImage_fullSpan M) η)
  obtain ⟨hfg, hspan, he⟩ := hd.exists_pure_fullLatticeGaugeFamily_eq
    (originalPrescribedTraceDualFamily_isHermitian M hξ).1 hp
  dsimp only [δ, hξ, ξ, L] at he
  simpa only [originalPrescribedTraceDualFamily_globalUnitBallModule M η hη] using he

attribute [local instance] normalizedNumberFieldAdelicStructure_isProper

/-- The maximal slope of the actual original trace-dual full-lattice bundle,
with the prescribed trace metric, including the zero-rank conventions. -/
theorem originalPrescribedTraceDual_maximalSlope
    (η : NormFamily (normalizedNumberFieldAdelicStructure K)
      (K ⊗[NumberField.RingOfIntegers K] M))
    (hη : η.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    let L := genericImage (K := K) M
    let V := fullLatticeAdelicBundle L (genericImage_fg M) (genericImage_fullSpan M) η
    let hV : V.IsHermitian normalizedNumberFieldArchimedeanCompletions :=
      fullLatticeGaugeFamily_isHermitian L (genericImage_fg M) (genericImage_fullSpan M) η hη
    let T := codifferentModule K ⊗[NumberField.RingOfIntegers K]
      Module.Dual (NumberField.RingOfIntegers K) M
    let δ := originalPrescribedTraceDualFamily M hV
    let W := fullLatticeAdelicBundle (genericImage (K := K) T) (genericImage_fg T)
      (genericImage_fullSpan T) δ
    W.maximalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions =
      ((Real.log |(NumberField.discr K : ℝ)| -
        2 * (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) * Real.log 2 : ℝ) : EReal) -
          V.minimalSlope (Or.inl inferInstance) normalizedNumberFieldArchimedeanCompletions := by
  let L := genericImage (K := K) M
  let V := fullLatticeAdelicBundle L (genericImage_fg M) (genericImage_fullSpan M) η
  let hV := fullLatticeGaugeFamily_isHermitian L (genericImage_fg M)
    (genericImage_fullSpan M) η hη
  let T := codifferentModule K ⊗[NumberField.RingOfIntegers K]
    Module.Dual (NumberField.RingOfIntegers K) M
  let δ := originalPrescribedTraceDualFamily M hV
  let W := fullLatticeAdelicBundle (genericImage (K := K) T) (genericImage_fg T)
    (genericImage_fullSpan T) δ
  let hS : DiscreteMeasurableSpace (normalizedNumberFieldAdelicStructure K).Ω ∨
      (normalizedNumberFieldAdelicStructure K).HasCommonCountableDenseSubfield :=
    Or.inl inferInstance
  let hN := normalizedNumberFieldArchimedeanCompletions (K := K)
  let Q := dualizingLine K
  let hQ := dualizingLine_isHermitian K
  let D := V.dualOfMeasurableBase hS
  let P := D.orthogonalTensorPair Q hS hN hV.dual hQ
  have hW : W.toNormFamily = δ :=
    originalPrescribedTraceDualFamily_eq_fullLatticeGaugeFamily M η hη
  have hs : W.maximalSlope hS hN = P.maximalSlope hS hN := by
    apply W.maximalSlope_eq_of_completed_isometry P (traceTensorGenericPairEquiv M) hS hN
    intro ω z
    rw [hW]
    rfl
  change W.maximalSlope hS hN = _
  rw [hs, maximalSlope_orthogonalTensor_scalarLine D Q hS hN hV.dual hQ]
  rw [maximalSlope_dual_eq_neg_minimalSlope V hS hN hV]
  rw [NumberFieldTraceDualizingLineCovolume.dualizingLine_degree]
  change -V.minimalSlope hS hN + _ = _ - V.minimalSlope hS hN
  exact (add_comm _ _).trans (sub_eq_add_neg _ _).symm

end NumberField

end ArakelovGeometry.NumberFieldClassicalTraceDualSlope

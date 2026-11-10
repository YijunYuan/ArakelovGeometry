/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.BasisComparison
public import ArakelovGeometry.AdelicVectorBundle.Hermitian
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Dominated Hermitian basis families

The base-field construction in Remark 4.1.14 uses the coordinate maximum at
finite places and the Euclidean coordinate norm at infinite places. These
norms are transported through the actual completed basis. Hermitianity uses
the explicit usual Archimedean normalization of the completed fields.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)
  (E : Type w) [AddCommGroup E] [Module K E]

/-- The Euclidean coordinate norm on each actual completed fibre. -/
def ofBasisEuclidean {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) : NormFamily S E where
  norm ω := (normSeminorm (S.ϕ ω).Completion (PiLp 2 (fun _ : ι => (S.ϕ ω).Completion))).comp
    (((b.baseChange (S.ϕ ω).Completion).equivFun.trans
      (WithLp.linearEquiv 2 (S.ϕ ω).Completion (ι → (S.ϕ ω).Completion)).symm).toLinearMap)
  norm_eq_zero_iff ω x := by
    change ‖(WithLp.linearEquiv 2 (S.ϕ ω).Completion (ι → (S.ϕ ω).Completion)).symm
      ((b.baseChange (S.ϕ ω).Completion).equivFun x)‖ = 0 ↔ x = 0
    rw [norm_eq_zero, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

/-- The max-finite, Euclidean-infinite basis family in Remark 4.1.14.
Its Hermitian property under the usual normalization is proved below. -/
def ofBasisHermitian {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) : NormFamily S E := by
  classical
  exact
    { norm := fun ω => if ω ∈ S.Ωinf then (ofBasisEuclidean S E b).norm ω
        else (ofBasis S E b).norm ω
      norm_eq_zero_iff := fun ω x => by
        split_ifs <;> exact norm_eq_zero_iff _ ω x }

variable {S E} {ι : Type*} [Fintype ι] (b : Module.Basis ι K E)

/-- The exact square-root-of-squares coordinate formula, including rank zero. -/
theorem ofBasisEuclidean_norm (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasisEuclidean S E b).norm ω x =
      Real.sqrt (∑ i, ‖(b.baseChange (S.ϕ ω).Completion).equivFun x i‖ ^ 2) :=
  PiLp.norm_eq_of_L2 _

/-- At a finite place the Hermitian basis family is the coordinate maximum. -/
theorem ofBasisHermitian_norm_of_finite (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasisHermitian S E b).norm ω x = (ofBasis S E b).norm ω x := by
  have hn : ω ∉ S.Ωinf := fun h => h hω
  simp only [ofBasisHermitian, ite_eq_right hn]

/-- At an infinite place the Hermitian basis family is the Euclidean norm. -/
theorem ofBasisHermitian_norm_of_infinite (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasisHermitian S E b).norm ω x =
      Real.sqrt (∑ i, ‖(b.baseChange (S.ϕ ω).Completion).equivFun x i‖ ^ 2) := by
  simp only [ofBasisHermitian, ite_eq_left hω, ofBasisEuclidean_norm]

/-- The Euclidean coordinate formula for rational vectors uses only their
rational coordinates and the original absolute-value family. -/
theorem ofBasisEuclidean_norm_rational (ω : S.Ω) (x : E) :
    (ofBasisEuclidean S E b).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) =
      Real.sqrt (∑ i, ((S.ϕ ω) (b.equivFun x i)) ^ 2) := by
  simp only [ofBasisEuclidean_norm, basis_equivFun_one_tmul, S.norm_algebraMap_eq_absValue]

open Classical in
/-- The mixed Hermitian rational norm is a measurable finite coordinate formula. -/
theorem ofBasisHermitian_norm_rational (ω : S.Ω) (x : E) :
    (ofBasisHermitian S E b).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) =
      if ω ∈ S.Ωinf then Real.sqrt (∑ i, ((S.ϕ ω) (b.equivFun x i)) ^ 2)
      else ‖fun i => (S.ϕ ω) (b.equivFun x i)‖ := by
  classical
  by_cases hω : ω ∈ S.Ωinf
  · simp only [ofBasisHermitian, ite_eq_left hω, ofBasisEuclidean_norm_rational]
  · simp only [ofBasisHermitian, ite_eq_right hω, ofBasis_norm_rational]

/-- The Hermitian basis family has measurable rational evaluations. -/
theorem ofBasisHermitian_isMeasurable : (ofBasisHermitian S E b).IsMeasurable := by
  classical
  intro x
  simp only [ofBasisHermitian_norm_rational]
  apply Measurable.ite S.measurableSet_Ωinf
  · exact (Finset.measurable_sum _ fun i _ =>
      (S.measurable_absValue (b.equivFun x i)).pow_const 2).sqrt
  · exact (Measurable.of_eval fun i => S.measurable_absValue (b.equivFun x i)).norm

/-- The finite-place branch is ultrametric in every dimension. -/
theorem ofBasisHermitian_isUltrametric : (ofBasisHermitian S E b).IsUltrametric := by
  intro ω hω x y
  simpa only [ofBasisHermitian_norm_of_finite b ω hω,
    ofBasisMixed_norm_of_finite b ω hω] using ofBasisMixed_isUltrametric b ω hω x y

/-- The actual completed coordinate isometry pulls the canonical Euclidean
inner product back to the prescribed fibre norm and scalar action. -/
theorem ofBasisHermitian_isHermitian
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ofBasisHermitian S E b).IsHermitian hS := by
  refine ⟨ofBasisHermitian_isUltrametric b, fun ω hω => ?_⟩
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := (ofBasisHermitian S E b).fibreNormedAddCommGroup ω
  let := (ofBasisHermitian S E b).fibreNormedSpace ω
  have : InnerProductSpaceable (PiLp 2 (fun _ : ι => (S.ϕ ω).Completion)) :=
    InnerProductSpace.toInnerProductSpaceable (S.ϕ ω).Completion
  let f := (b.baseChange (S.ϕ ω).Completion).equivFun.trans
    (WithLp.linearEquiv 2 (S.ϕ ω).Completion (ι → (S.ϕ ω).Completion)).symm
  apply exists_innerProductCore_iff_innerProductSpaceable.mpr
  apply innerProductSpaceable_of_norm_preserving_addMonoidHom f.toAddMonoidHom
  intro x
  change ‖f x‖ = (ofBasisHermitian S E b).norm ω x
  rw [ofBasisHermitian_norm_of_infinite b ω hω]
  exact PiLp.norm_eq_of_L2 _

/-- The Euclidean coordinate norm is bounded by the coordinate sum. -/
theorem ofBasisHermitian_le_ofBasisMixed : ofBasisHermitian S E b ≤ ofBasisMixed S E b := by
  intro ω x
  by_cases hω : ω ∈ S.Ωinf
  · rw [ofBasisHermitian_norm_of_infinite b ω hω, ofBasisMixed_norm_of_infinite b ω hω]
    exact Real.sqrt_le_iff.mpr
      ⟨Finset.sum_nonneg (fun i _ => _root_.norm_nonneg _),
        Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => _root_.norm_nonneg _)⟩
  · rw [ofBasisHermitian_norm_of_finite b ω (not_not.mp hω),
      ofBasisMixed_norm_of_finite b ω (not_not.mp hω)]

/-- Cauchy–Schwarz gives the exact square-root-of-rank loss at an infinite
place, including the empty basis. -/
theorem ofBasisMixed_norm_le_sqrt_card_mul_of_infinite (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasisMixed S E b).norm ω x ≤
      Real.sqrt (Fintype.card ι : ℝ) * (ofBasisHermitian S E b).norm ω x := by
  rw [ofBasisMixed_norm_of_infinite b ω hω, ofBasisHermitian_norm_of_infinite b ω hω]
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι => (1 : ℝ))
      (fun i => ‖(b.baseChange (S.ϕ ω).Completion).equivFun x i‖)

variable [FiniteDimensional K E]

/-- The precise distance estimate in Remark 4.1.14: one half of the log
rank at infinite places, and zero at finite places. -/
theorem ofBasisHermitian_localDist_ofBasisMixed_le (ω : S.Ω) :
    (ofBasisHermitian S E b).localDist (ofBasisMixed S E b) ω ≤
      S.Ωinf.indicator (fun _ => (1 / 2 : ℝ) * Real.log (Fintype.card ι : ℝ)) ω := by
  classical
  have hlog : 0 ≤ (1 / 2 : ℝ) * Real.log (Fintype.card ι : ℝ) :=
    mul_nonneg (by norm_num) (Real.log_natCast_nonneg _)
  apply ((ofBasisHermitian S E b).localDist_le_iff_norm_le (ofBasisMixed S E b) ω
    (Set.indicator_nonneg (fun _ _ => hlog) ω)).mpr
  intro x
  by_cases hω : ω ∈ S.Ωinf
  · rw [Set.indicator_of_mem hω]
    constructor
    · exact (ofBasisHermitian_le_ofBasisMixed b ω x).trans
        (le_mul_of_one_le_left ((ofBasisMixed S E b).norm_nonneg ω x)
          (Real.one_le_exp_iff.mpr hlog))
    · apply (ofBasisMixed_norm_le_sqrt_card_mul_of_infinite b ω hω x).trans
      apply mul_le_mul_of_nonneg_right _ ((ofBasisHermitian S E b).norm_nonneg ω x)
      by_cases hc : Fintype.card ι = 0
      · simp [hc]
      · rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hc),
          mul_comm]
  · simp only [Set.indicator_of_notMem hω, Real.exp_zero, one_mul,
      ofBasisHermitian_norm_of_finite b ω (not_not.mp hω),
      ofBasisMixed_norm_of_finite b ω (not_not.mp hω), le_refl, and_self]

/-- The exact distance correction has integrable envelopes on every adelic
structure with finite Archimedean measure. -/
theorem ofBasisHermitian_localDist_hasIntegrableBounds (hfin : S.v S.Ωinf < ⊤) :
    HasIntegrableBounds ((ofBasisHermitian S E b).localDist (ofBasisMixed S E b)) S.v := by
  refine ⟨⟨S.Ωinf.indicator (fun _ => (1 / 2 : ℝ) * Real.log (Fintype.card ι : ℝ)), ?_,
    Filter.Eventually.of_forall (ofBasisHermitian_localDist_ofBasisMixed_le b)⟩,
    ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall ?_⟩⟩
  · exact (integrable_indicator_iff S.measurableSet_Ωinf).mpr (integrableOn_const hfin.ne)
  · intro ω
    exact (ofBasisHermitian S E b).localDist_nonneg _ ω

/-- The quantitative comparison gives strong domination of this explicit
family, without presupposing any domination of its norms. -/
theorem ofBasisHermitian_isStronglyDominated_of_measure_lt_top (hfin : S.v S.Ωinf < ⊤) :
    (ofBasisHermitian S E b).IsStronglyDominated :=
  (isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top
    b (ofBasisHermitian S E b) hfin).mpr (ofBasisHermitian_localDist_hasIntegrableBounds b hfin)

/-- Domination of the Hermitian basis family in Remark 4.1.14. -/
theorem ofBasisHermitian_isDominated
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ofBasisHermitian S E b).IsDominated :=
  (ofBasisHermitian_isStronglyDominated_of_measure_lt_top b
    (S.v_Ωinf_lt_top_of_isRCLike hS)).1

/-- Its rational logarithmic norms are integrable, including the zero vector. -/
theorem ofBasisHermitian_integrable_logNorm
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (x : E) :
    Integrable ((ofBasisHermitian S E b).logNorm x) S.v :=
  (ofBasisHermitian_isDominated b hS).integrable_logNorm (ofBasisHermitian_isMeasurable b) x

variable (S E)

/-- Every finite-dimensional space admits a dominated measurable Hermitian
norm family under the usual Archimedean normalization. The witness is the
explicit max-finite, Euclidean-infinite completed-basis construction. -/
theorem exists_hermitian_dominated_measurable
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ∃ ξ : NormFamily S E, ξ.IsHermitian hS ∧ ξ.IsDominated ∧ ξ.IsMeasurable :=
  ⟨ofBasisHermitian S E (Module.finBasis K E),
    ofBasisHermitian_isHermitian (Module.finBasis K E) hS,
    ofBasisHermitian_isDominated (Module.finBasis K E) hS,
    ofBasisHermitian_isMeasurable (Module.finBasis K E)⟩

variable {S E}

private theorem euclidean_functional_norm {L : Type*} [RCLike L]
    {ι : Type*} [Fintype ι] (f : EuclideanSpace L ι →L[L] L) :
    ‖f‖ = Real.sqrt (∑ i, ‖f ((EuclideanSpace.basisFun ι L) i)‖ ^ 2) := by
  obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual L (EuclideanSpace L ι)).surjective f
  rw [LinearIsometryEquiv.norm_map]
  simp only [InnerProductSpace.toDual_apply_apply]
  rw [(EuclideanSpace.basisFun ι L).sum_sq_norm_inner_left,
    Real.sqrt_sq (_root_.norm_nonneg _)]

/-- At an infinite place with its usual norm, the actual completed dual
Hermitian basis norm is the Euclidean norm of the evaluation coordinates. -/
theorem ofBasisHermitian_dual_norm_of_infinite (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (hL : IsRCLikeNormedField (S.ϕ ω).Completion)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    (ofBasisHermitian S E b).dual.norm ω z =
      Real.sqrt (∑ i, ‖dualBaseChangeEquiv K (S.ϕ ω).Completion E z
        ((b.baseChange (S.ϕ ω).Completion) i)‖ ^ 2) := by
  classical
  let := hL
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := (ofBasisHermitian S E b).fibreNormedAddCommGroup ω
  let := (ofBasisHermitian S E b).fibreNormedSpace ω
  let e : ((S.ϕ ω).Completion ⊗[K] E) ≃ₗᵢ[(S.ϕ ω).Completion]
      EuclideanSpace (S.ϕ ω).Completion ι :=
    { toLinearEquiv := (b.baseChange (S.ϕ ω).Completion).equivFun.trans
        (WithLp.linearEquiv 2 (S.ϕ ω).Completion (ι → (S.ϕ ω).Completion)).symm
      norm_map' := fun x => by
        change ‖(WithLp.linearEquiv 2 (S.ϕ ω).Completion
          (ι → (S.ϕ ω).Completion)).symm
            ((b.baseChange (S.ϕ ω).Completion).equivFun x)‖ =
          (ofBasisHermitian S E b).norm ω x
        rw [ofBasisHermitian_norm_of_infinite b ω hω]
        exact PiLp.norm_eq_of_L2 _ }
  have he (i : ι) : e ((b.baseChange (S.ϕ ω).Completion) i) =
      (EuclideanSpace.basisFun ι (S.ϕ ω).Completion) i := by
    change (WithLp.linearEquiv 2 (S.ϕ ω).Completion (ι → (S.ϕ ω).Completion)).symm
      ((b.baseChange (S.ϕ ω).Completion).equivFun
        ((b.baseChange (S.ϕ ω).Completion) i)) = _
    rw [EuclideanSpace.basisFun_apply]
    ext j
    simp [EuclideanSpace.single, Finsupp.single_apply, eq_comm]
  have he' (i : ι) : e.symm ((EuclideanSpace.basisFun ι (S.ϕ ω).Completion) i) =
      (b.baseChange (S.ϕ ω).Completion) i := by
    rw [← he, e.symm_apply_apply]
  let f := LinearMap.toContinuousLinearMap (dualBaseChangeEquiv K (S.ϕ ω).Completion E z)
  calc
    (ofBasisHermitian S E b).dual.norm ω z = ‖f‖ :=
      linearMapOperatorSeminorm_coe_continuousLinearMap f
    _ = ‖f.comp (e.symm : EuclideanSpace (S.ϕ ω).Completion ι →L[(S.ϕ ω).Completion]
        ((S.ϕ ω).Completion ⊗[K] E))‖ :=
      (f.opNorm_comp_linearIsometryEquiv e.symm).symm
    _ = _ := by
      rw [euclidean_functional_norm]
      change Real.sqrt (∑ i, ‖f (e.symm
        ((EuclideanSpace.basisFun ι (S.ϕ ω).Completion) i))‖ ^ 2) = _
      simp only [he']
      rfl

/-- The actual completed dual Hermitian family is the same explicit
construction on the rational dual basis. -/
theorem ofBasisHermitian_dual [DecidableEq ι]
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ofBasisHermitian S E b).dual = ofBasisHermitian S (Module.Dual K E) b.dualBasis := by
  ext ω z
  by_cases hω : ω ∈ S.Ωinf
  · rw [ofBasisHermitian_dual_norm_of_infinite b ω hω (hS ω hω),
      ofBasisHermitian_norm_of_infinite b.dualBasis ω hω]
    simp only [dualBaseChange_apply_basis_eq]
  · have hf : ω ∈ S.Ωfin := not_not.mp hω
    have he : (ofBasisHermitian S E b).dual.norm ω z =
        (ofBasisMixed S E b).dual.norm ω z := by
      simp only [dual_norm_eq_sSup, ofBasisHermitian_norm_of_finite b ω hf,
        ofBasisMixed_norm_of_finite b ω hf]
    rw [he, ofBasisMixed_dual, ofBasisHermitian_norm_of_finite b.dualBasis ω hf]

/-- Strict measurability of the actual dual follows from its exact rational
dual-basis coordinate formula, without a countability assumption on the field. -/
theorem ofBasisHermitian_dual_isMeasurable
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ofBasisHermitian S E b).dual.IsMeasurable := by
  classical
  rw [ofBasisHermitian_dual b hS]
  exact ofBasisHermitian_isMeasurable b.dualBasis

/-- The dual rational logarithmic norms are integrable too. -/
theorem ofBasisHermitian_dual_integrable_logNorm
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (ℓ : Module.Dual K E) : Integrable ((ofBasisHermitian S E b).dual.logNorm ℓ) S.v :=
  (ofBasisHermitian_isDominated b hS).dual.integrable_logNorm
    (ofBasisHermitian_dual_isMeasurable b hS) ℓ

end ArakelovGeometry.NormFamily

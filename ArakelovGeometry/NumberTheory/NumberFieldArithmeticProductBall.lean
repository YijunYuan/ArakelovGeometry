/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberFieldHermitianBasisCovolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The actual arithmetic product ball and its ordinary Euclidean measure
-/

@[expose] public section

noncomputable section

open NumberField MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NumberFieldArithmeticProductBall

open AdelicStructure NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanEuclidean
  NumberFieldArchimedeanWeightedJacobian

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The body in the original completed product, cut out by every original infinite norm. -/
def productBall (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (R : ℝ) :
    Set (CompletedVectorProduct K E) :=
  {z | ∀ w : InfinitePlace K, ξ.norm (normalizedInfinitePlacePoint w) (z w) ≤ R}

/-- Canonical ordinary Euclidean volume, on the same original product as its lattice covolume. -/
def productBallVolume (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) (R : ℝ) : ENNReal := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  exact volume (productBall ξ R)

omit [FiniteDimensional K E] in
/-- Convexity uses the actual coordinate norms and the prescribed real action. -/
theorem convex_productBall (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (R : ℝ) :
    Convex ℝ (productBall ξ R) := by
  let : ∀ w : InfinitePlace K, NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let : ∀ w : InfinitePlace K, NormedSpace ℝ (CompletedCoefficient w ⊗[K] E) :=
    fun w => fibreRealNormedSpace ξ w
  intro x hx y hy a b ha hb hab w
  change ‖a • x w + b • y w‖ ≤ R
  calc
    _ ≤ ‖a • x w‖ + ‖b • y w‖ := norm_add_le _ _
    _ = a * ‖x w‖ + b * ‖y w‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * R + b * R := add_le_add
      (mul_le_mul_of_nonneg_left (hx w) ha) (mul_le_mul_of_nonneg_left (hy w) hb)
    _ = R := by rw [← add_mul, hab, one_mul]

omit [FiniteDimensional K E] in
/-- Symmetry is literal negation in the original completed product. -/
theorem neg_productBall (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) (R : ℝ) :
    -productBall ξ R = productBall ξ R := by
  ext z
  simp only [Set.mem_neg, productBall, Set.mem_ofPred_eq, Pi.neg_apply, map_neg_eq_map]

omit [FiniteDimensional K E] in
/-- The actual arithmetic product body is closed for the ordinary L2 topology. -/
theorem productBall_isClosed (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (R : ℝ) :
    letI := euclideanNormedAddCommGroup ξ
    IsClosed (productBall ξ R) := by
  let : ∀ w : InfinitePlace K, NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let : ∀ w : InfinitePlace K, NormedSpace ℝ (CompletedCoefficient w ⊗[K] E) :=
    fun w => fibreRealNormedSpace ξ w
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let : SeminormedAddCommGroup (CompletedVectorProduct K E) :=
    (euclideanNormedAddCommGroup ξ).toSeminormedAddCommGroup
  let : TopologicalSpace (CompletedVectorProduct K E) :=
    @UniformSpace.toTopologicalSpace _
      (euclideanNormedAddCommGroup ξ).toMetricSpace.toPseudoMetricSpace.toUniformSpace
  rw [show productBall ξ R = ⋂ w : InfinitePlace K,
      {z : CompletedVectorProduct K E | ξ.norm (normalizedInfinitePlacePoint w) (z w) ≤ R}
    from by ext z; simp [productBall]]
  apply isClosed_iInter
  intro w
  apply isClosed_le ?_ continuous_const
  exact ((PiLp.proj (𝕜 := ℝ) 2
    (fun w : InfinitePlace K => CompletedCoefficient w ⊗[K] E) w).continuous.comp
    (euclideanIsometry ξ).continuous).norm

/-- Compactness is proved in the original real product, with no measure premise. -/
theorem productBall_isCompact (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    {R : ℝ} (hR : 0 ≤ R) :
    letI := euclideanNormedAddCommGroup ξ
    IsCompact (productBall ξ R) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  have hsub : productBall ξ R ⊆ Metric.closedBall 0
      (Real.sqrt ((Fintype.card (InfinitePlace K) : ℝ) * R ^ 2)) := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖z‖ ^ 2 ≤ (Fintype.card (InfinitePlace K) : ℝ) * R ^ 2 := by
      rw [euclidean_norm_sq]
      calc
        _ ≤ ∑ _w : InfinitePlace K, R ^ 2 := Finset.sum_le_sum fun w _ =>
          (sq_le_sq₀ (ξ.norm_nonneg _ _) hR).mpr (hz w)
        _ = _ := by simp
    have hsqrt := Real.sq_sqrt
      (mul_nonneg (Nat.cast_nonneg (Fintype.card (InfinitePlace K))) (sq_nonneg R))
    have hn := norm_nonneg z
    have hr := Real.sqrt_nonneg ((Fintype.card (InfinitePlace K) : ℝ) * R ^ 2)
    nlinarith
  exact (isCompact_closedBall (0 : CompletedVectorProduct K E) _).of_isClosed_subset
    (productBall_isClosed ξ R) hsub

/-- The original Hermitian fibre norm gives its inner product for the fixed real action. -/
@[instance_reducible]
def fibreRealInnerProduct
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) (w : InfinitePlace K) :
    letI := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
    letI := fibreRealNormedSpace ξ w
    InnerProductSpace ℝ (CompletedCoefficient w ⊗[K] E) := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  apply InnerProductSpace.ofNorm ℝ
  intro x y
  exact (NormFamily.isHermitian_iff_parallelogram.mp hξ).2
    (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w) x y

/-- A real orthonormal basis of the original completed Hermitian fibre. -/
def fibreRealBasis (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) (w : InfinitePlace K) :
    letI := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
    letI := fibreRealNormedSpace ξ w
    letI := fibreRealInnerProduct hξ w
    OrthonormalBasis (Fin (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E))) ℝ
      (CompletedCoefficient w ⊗[K] E) := by
  let := ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := fibreRealNormedSpace ξ w
  let := fibreRealInnerProduct hξ w
  let : FiniteDimensional ℝ (CompletedCoefficient w ⊗[K] E) := finite_completedFibreReal w
  exact stdOrthonormalBasis ℝ _

/-- The real coordinates retain their actual infinite-place blocks. -/
abbrev RealCoordinateIndex :=
  (w : InfinitePlace K) × Fin (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E))

/-- The actual original-product coordinate equivalence in fibre orthonormal coordinates. -/
def realCoordinateEquiv (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    CompletedVectorProduct K E ≃ₗ[ℝ] (RealCoordinateIndex (K := K) (E := E) → ℝ) := by
  let : ∀ w : InfinitePlace K, NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let : ∀ w : InfinitePlace K, NormedSpace ℝ (CompletedCoefficient w ⊗[K] E) :=
    fun w => fibreRealNormedSpace ξ w
  let : ∀ w : InfinitePlace K, InnerProductSpace ℝ (CompletedCoefficient w ⊗[K] E) :=
    fun w => fibreRealInnerProduct hξ w
  exact (Pi.basis (fun w => (fibreRealBasis ξ hξ w).toBasis)).equivFun

/-- Parseval's identity for each original completed fibre, with ordinary real coordinates. -/
theorem fibre_norm_sq_coordinates (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) (w : InfinitePlace K)
    (z : CompletedVectorProduct K E) :
    (ξ.norm (normalizedInfinitePlacePoint w) (z w)) ^ 2 =
      ∑ i, (realCoordinateEquiv ξ hξ z ⟨w, i⟩) ^ 2 := by
  let : ∀ w : InfinitePlace K, NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let : ∀ w : InfinitePlace K, NormedSpace ℝ (CompletedCoefficient w ⊗[K] E) :=
    fun w => fibreRealNormedSpace ξ w
  let : ∀ w : InfinitePlace K, InnerProductSpace ℝ (CompletedCoefficient w ⊗[K] E) :=
    fun w => fibreRealInnerProduct hξ w
  have h := (fibreRealBasis ξ hξ w).repr.norm_map (z w)
  change ‖z w‖ ^ 2 = _
  rw [← h, PiLp.norm_sq_eq_of_L2]
  congr 1
  funext i
  simp only [realCoordinateEquiv, Module.Basis.equivFun_apply, Real.norm_eq_abs, sq_abs]
  rw [Pi.basis_repr]
  rfl

/-- The original completed product is isometric to its blockwise ordinary real coordinates. -/
def realCoordinateIsometry (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    CompletedVectorProduct K E ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (RealCoordinateIndex (K := K) (E := E)) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  refine { (realCoordinateEquiv ξ hξ).trans
    (WithLp.linearEquiv 2 ℝ (RealCoordinateIndex (K := K) (E := E) → ℝ)).symm with
      norm_map' := ?_ }
  intro z
  change ‖WithLp.toLp 2 (realCoordinateEquiv ξ hξ z)‖ = ‖z‖
  have hsq : ‖WithLp.toLp 2 (realCoordinateEquiv ξ hξ z)‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, euclidean_norm_sq, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro w _
    simpa only [Real.norm_eq_abs, sq_abs] using (fibre_norm_sq_coordinates ξ hξ w z).symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The actual block coordinate equivalence preserves canonical ordinary Euclidean volume. -/
theorem realCoordinateEquiv_measurePreserving
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanInnerProduct hξ
    letI : MeasurableSpace (CompletedVectorProduct K E) := borel _
    letI : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
    MeasurePreserving (realCoordinateEquiv ξ hξ) volume volume := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  exact (PiLp.volume_preserving_ofLp (RealCoordinateIndex (K := K) (E := E))).comp
    (realCoordinateIsometry ξ hξ).measurePreserving

/-- The ordinary real coordinate box, with a separate dimension-normalized radius in each fibre. -/
def coordinateCube (R : ℝ) : Set (RealCoordinateIndex (K := K) (E := E) → ℝ) :=
  Set.pi Set.univ (fun q => Set.Icc
    (-(R / Real.sqrt (Module.finrank ℝ (CompletedCoefficient q.1 ⊗[K] E) : ℝ)))
    (R / Real.sqrt (Module.finrank ℝ (CompletedCoefficient q.1 ⊗[K] E) : ℝ)))

/-- The dimension-normalized cube lies in the literal product of original fibre balls. -/
theorem coordinateCube_preimage_subset_productBall
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (hn : 0 < Module.finrank K E) {R : ℝ} (hR : 0 ≤ R) :
    (realCoordinateEquiv ξ hξ) ⁻¹' coordinateCube (K := K) (E := E) R ⊆ productBall ξ R := by
  intro z hz w
  have hN : 0 < Module.finrank ℝ (CompletedCoefficient w ⊗[K] E) := by
    rw [completedFibre_real_finrank]
    exact Nat.mul_pos InfinitePlace.mult_pos hn
  have hNr : 0 < (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E) : ℝ) := Nat.cast_pos.mpr hN
  have hsq : (ξ.norm (normalizedInfinitePlacePoint w) (z w)) ^ 2 ≤ R ^ 2 := by
    rw [fibre_norm_sq_coordinates ξ hξ w z]
    calc
      _ ≤ ∑ _i : Fin (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E)),
          (R / Real.sqrt (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E) : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := (Set.mem_pi.mp hz) ⟨w, i⟩ (Set.mem_univ _)
        have ha := abs_le.mpr hi
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (div_nonneg hR (Real.sqrt_nonneg _))).mpr ha
      _ = R ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [div_pow, Real.sq_sqrt hNr.le]
        field_simp
  exact (sq_le_sq₀ (ξ.norm_nonneg _ _) hR).mp hsq

/-- Exact ordinary volume of the actual inverse-image cube, without a volume premise. -/
theorem volume_coordinateCube_preimage
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions) (R : ℝ) :
    letI := euclideanNormedAddCommGroup ξ
    letI := euclideanNormedSpace ξ
    letI := euclideanInnerProduct hξ
    letI : MeasurableSpace (CompletedVectorProduct K E) := borel _
    letI : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
    volume ((realCoordinateEquiv ξ hξ) ⁻¹' coordinateCube (K := K) (E := E) R) =
      ∏ w : InfinitePlace K,
        ENNReal.ofReal (2 * R /
          Real.sqrt (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E) : ℝ)) ^
            Module.finrank ℝ (CompletedCoefficient w ⊗[K] E) := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  have hm : MeasurableSet (coordinateCube (K := K) (E := E) R) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
  rw [(realCoordinateEquiv_measurePreserving ξ hξ).measure_preimage hm.nullMeasurableSet,
    coordinateCube, volume_pi, Measure.pi_pi, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro w _
  calc
    _ = ∏ _i : Fin (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E)),
        ENNReal.ofReal (2 * R /
          Real.sqrt (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E) : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Real.volume_Icc]
      congr 1
      ring
    _ = _ := by simp

/-- A concrete lower bound for the original body from actual ordinary coordinate cubes. -/
theorem productBallVolume_ge_coordinateCube
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (hn : 0 < Module.finrank K E) {R : ℝ} (hR : 0 ≤ R) :
    (∏ w : InfinitePlace K,
      ENNReal.ofReal (2 * R /
        Real.sqrt (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E) : ℝ)) ^
          Module.finrank ℝ (CompletedCoefficient w ⊗[K] E)) ≤ productBallVolume ξ hξ R := by
  let := euclideanNormedAddCommGroup ξ
  let := euclideanNormedSpace ξ
  let := euclideanInnerProduct hξ
  let : MeasurableSpace (CompletedVectorProduct K E) := borel _
  let : BorelSpace (CompletedVectorProduct K E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := CompletedVectorProduct K E)
  rw [← volume_coordinateCube_preimage ξ hξ R]
  exact measure_mono (coordinateCube_preimage_subset_productBall ξ hξ hn hR)

omit [NumberField K] in
private theorem cubeFactor_eq (n : ℕ) (hn : 0 < n) (R : ℝ) (w : InfinitePlace K) :
    (2 * R / Real.sqrt ((w.mult * n : ℕ) : ℝ)) ^ (w.mult * n) =
      (2 : ℝ) ^ n * (R / Real.sqrt (n : ℝ)) ^ (w.mult * n) := by
  classical
  by_cases hw : w.IsReal
  · simp only [hw.mult_eq_one, one_mul]
    rw [mul_div_assoc, mul_pow]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    simp only [hc.mult_eq_two, Nat.cast_mul, Nat.cast_ofNat, pow_mul]
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hb : (2 * R / Real.sqrt (2 * (n : ℝ))) ^ 2 =
        2 * (R / Real.sqrt (n : ℝ)) ^ 2 := by
      simp only [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (n : ℝ)),
        Real.sq_sqrt hnR.le]
      field_simp
    rw [hb, mul_pow]

/-- Scalar simplification of the actual fibre cube volumes, with the original field degree. -/
theorem coordinateCube_volume_product_eq {R : ℝ} (hR : 0 ≤ R)
    (hn : 0 < Module.finrank K E) :
    (∏ w : InfinitePlace K,
      ENNReal.ofReal (2 * R /
        Real.sqrt (Module.finrank ℝ (CompletedCoefficient w ⊗[K] E) : ℝ)) ^
          Module.finrank ℝ (CompletedCoefficient w ⊗[K] E)) =
      ENNReal.ofReal ((2 : ℝ) ^ (Module.finrank K E * Fintype.card (InfinitePlace K)) *
        (R / Real.sqrt (Module.finrank K E : ℝ)) ^
          (Module.finrank ℚ K * Module.finrank K E)) := by
  simp only [completedFibre_real_finrank]
  have hnonneg (w : InfinitePlace K) :
      0 ≤ 2 * R / Real.sqrt ((w.mult * Module.finrank K E : ℕ) : ℝ) := by positivity
  calc
    _ = ENNReal.ofReal (∏ w : InfinitePlace K,
        (2 * R / Real.sqrt ((w.mult * Module.finrank K E : ℕ) : ℝ)) ^
          (w.mult * Module.finrank K E)) := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => pow_nonneg (hnonneg w) _)]
      apply Finset.prod_congr rfl
      intro w _
      exact (ENNReal.ofReal_pow (hnonneg w) _).symm
    _ = _ := by
      congr 1
      simp only [cubeFactor_eq _ hn, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ]
      rw [← pow_mul, Finset.prod_pow_eq_pow_sum, ← Finset.sum_mul, InfinitePlace.sum_mult_eq]

/-- The cube lower bound with the original rational rank and field degree. -/
theorem productBallVolume_ge_cube
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (hn : 0 < Module.finrank K E) {R : ℝ} (hR : 0 ≤ R) :
    ENNReal.ofReal ((2 : ℝ) ^ (Module.finrank K E * Fintype.card (InfinitePlace K)) *
      (R / Real.sqrt (Module.finrank K E : ℝ)) ^
        (Module.finrank ℚ K * Module.finrank K E)) ≤ productBallVolume ξ hξ R := by
  rw [← coordinateCube_volume_product_eq hR hn]
  exact productBallVolume_ge_coordinateCube ξ hξ hn hR

private theorem div_sqrt_pow_eq_rpow (n N : ℕ) (R : ℝ) :
    (R / Real.sqrt (n : ℝ)) ^ N =
      (n : ℝ) ^ (-((N : ℕ) : ℝ) / 2) * R ^ N := by
  have hpow : Real.sqrt (n : ℝ) ^ N = (n : ℝ) ^ ((N : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  rw [div_pow, hpow, div_eq_mul_inv,
    show -((N : ℕ) : ℝ) / 2 = -((N : ℝ) / 2) from by ring,
    Real.rpow_neg (Nat.cast_nonneg n)]
  exact mul_comm _ _

/-- The source cube constant for canonical ordinary Euclidean volume on the actual product. -/
theorem productBallVolume_cube_lower_bound
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (hn : 0 < Module.finrank K E) {R : ℝ} (hR : 0 ≤ R) :
    ENNReal.ofReal ((2 : ℝ) ^ (Module.finrank K E * Fintype.card (InfinitePlace K)) *
      (Module.finrank K E : ℝ) ^
        (-((Module.finrank ℚ K * Module.finrank K E : ℕ) : ℝ) / 2) *
          R ^ (Module.finrank ℚ K * Module.finrank K E)) ≤ productBallVolume ξ hξ R := by
  have h := productBallVolume_ge_cube ξ hξ hn hR
  rw [div_sqrt_pow_eq_rpow, ← mul_assoc] at h
  exact h

end ArakelovGeometry.NumberFieldArithmeticProductBall

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import ArakelovGeometry.Analysis.AbsoluteValue.Basic
import ArakelovGeometry.Analysis.AbsoluteValue.Ostrowski

/-!
# Root bounds for absolute values

Complex representations and finite-sum bounds provide the archimedean input
to the logarithmic root estimate in Chen–Moriwaki, Theorem 3.3.7.
-/

@[expose] public section

open UniformSpace

namespace AbsoluteValue

/-- An archimedean absolute value is a power of the norm of a complex embedding. -/
theorem exists_complex_embedding_of_not_isNonarchimedean {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ)
    (hv : ¬ IsNonarchimedean v) :
    ∃ (σ : K →+* ℂ) (s : ℝ), s ∈ Set.Ioc 0 1 ∧
      ∀ a : K, v a = ‖σ a‖ ^ s := by
  let := v.toNormedField
  have hc : ¬ IsNonarchimedean
      (Completion.instNormedFieldOfCompletableTopField K).toAbsoluteValue :=
    (isNonarchimedean_completion_iff v).not.mp hv
  rcases exists_ringEquiv_real_or_complex_of_complete
      (Completion.instNormedFieldOfCompletableTopField K).toAbsoluteValue
      hc (CauSeq.isComplete_completion v) with
    ⟨σ, s, hs, hσ⟩ | ⟨σ, s, hs, hσ⟩
  · refine ⟨Complex.ofRealHom.comp (σ.toRingHom.comp Completion.coeRingHom),
      s, hs, fun a ↦ ?_⟩
    have h := hσ (a : UniformSpace.Completion K)
    change ‖(a : UniformSpace.Completion K)‖ = ‖σ (a : UniformSpace.Completion K)‖ ^ s at h
    change v a = ‖(σ (a : UniformSpace.Completion K) : ℂ)‖ ^ s
    rw [Complex.norm_real]
    rw [UniformSpace.Completion.norm_coe] at h
    exact h
  · refine ⟨σ.toRingHom.comp Completion.coeRingHom, s, hs, fun a ↦ ?_⟩
    have h := hσ (a : UniformSpace.Completion K)
    change ‖(a : UniformSpace.Completion K)‖ = ‖σ (a : UniformSpace.Completion K)‖ ^ s at h
    change v a = ‖σ (a : UniformSpace.Completion K)‖ ^ s
    rw [UniformSpace.Completion.norm_coe] at h
    exact h

/-- Restriction to any subfield preserves and reflects the nonarchimedean property. -/
theorem isNonarchimedean_restriction_iff {K L : Type*} [Field K] [Field L]
    [Algebra K L] (w : AbsoluteValue L ℝ) :
    IsNonarchimedean (w.under K) ↔ IsNonarchimedean w := by
  constructor
  · intro hv
    by_contra hw
    obtain ⟨σ, s, hs, hσ⟩ := exists_complex_embedding_of_not_isNonarchimedean w hw
    have hw2 : 1 < w (2 : L) := by
      rw [hσ, map_ofNat]
      exact Real.one_lt_rpow (by norm_num) hs.1
    have hv2 := hv (1 : K) 1
    have hle : w (2 : L) ≤ 1 := by
      simpa [under, comp, one_add_one_eq_two, map_ofNat] using hv2
    exact (not_lt_of_ge hle) hw2
  · intro hw a b
    change w (algebraMap K L (a + b)) ≤
      max (w (algebraMap K L a)) (w (algebraMap K L b))
    rw [map_add]
    exact hw _ _

/-- The complex triangle inequality gives the cardinality factor to the correct power. -/
theorem sum_le_card_rpow_mul_of_complex_embedding {K : Type*} [Field K] (w : AbsoluteValue K ℝ)
    (σ : K →+* ℂ) {s : ℝ} (hs : 0 ≤ s)
    (hσ : ∀ a : K, w a = ‖σ a‖ ^ s)
    {ι : Type*} (t : Finset ι) (ht : t.Nonempty) (f : ι → K) {M : ℝ}
    (hM : ∀ i ∈ t, w (f i) ≤ M) :
    w (∑ i ∈ t, f i) ≤ (t.card : ℝ) ^ s * M := by
  obtain ⟨j, hj, hmax⟩ := t.exists_max_image (fun i ↦ ‖σ (f i)‖) ht
  rw [hσ, map_sum]
  have hsum : ‖∑ i ∈ t, σ (f i)‖ ≤ t.card * ‖σ (f j)‖ :=
    (norm_sum_le t _).trans ((Finset.sum_le_sum hmax).trans_eq (by simp))
  calc
    ‖∑ i ∈ t, σ (f i)‖ ^ s ≤ (t.card * ‖σ (f j)‖) ^ s :=
      Real.rpow_le_rpow (norm_nonneg _) hsum hs
    _ = (t.card : ℝ) ^ s * w (f j) := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (norm_nonneg _), hσ]
    _ ≤ (t.card : ℝ) ^ s * M :=
      mul_le_mul_of_nonneg_left (hM j hj) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- A finite-sum estimate gives the corresponding bound for a monic polynomial root. -/
theorem apply_root_le_of_sum_bound {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ)
    {p : Polynomial K} (hp : p.Monic) {a : L} (ha : Polynomial.aeval a p = 0)
    {A M : ℝ} (hA : 1 ≤ A) (hM : 1 ≤ M)
    (hcoeff : ∀ i < p.natDegree, w (algebraMap K L (p.coeff i)) ≤ M)
    (hsum : ∀ (f : ℕ → L) (B : ℝ), 0 ≤ B →
      (∀ i ∈ Finset.range p.natDegree, w (f i) ≤ B) →
      w (∑ i ∈ Finset.range p.natDegree, f i) ≤ A * B) :
    w a ≤ A * M := by
  have hm : 0 < p.natDegree := Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero hp ha
  have hrel : a ^ p.natDegree =
      -(∑ i ∈ Finset.range p.natDegree, algebraMap K L (p.coeff i) * a ^ i) := by
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ,
      hp.coeff_natDegree, one_smul] at ha
    simpa only [Algebra.smul_def] using (eq_neg_of_add_eq_zero_right ha)
  by_contra h
  have hr : A * M < w a := lt_of_not_ge h
  have hr1 : 1 < w a := (one_le_mul_of_one_le_of_one_le hA hM).trans_lt hr
  have hbound (i : ℕ) (hi : i ∈ Finset.range p.natDegree) :
      w (algebraMap K L (p.coeff i) * a ^ i) ≤ M * w a ^ (p.natDegree - 1) := by
    have hi' := Finset.mem_range.mp hi
    rw [map_mul, map_pow]
    apply mul_le_mul (hcoeff i (Finset.mem_range.mp hi))
      (pow_le_pow_right₀ hr1.le (by omega)) (pow_nonneg (w.nonneg a) _) (by linarith)
  have h := hsum (fun i ↦ algebraMap K L (p.coeff i) * a ^ i)
    (M * w a ^ (p.natDegree - 1))
    (mul_nonneg (by linarith) (pow_nonneg (w.nonneg a) _)) hbound
  have hwrel : w a ^ p.natDegree =
      w (∑ i ∈ Finset.range p.natDegree, algebraMap K L (p.coeff i) * a ^ i) := by
    rw [← map_pow, hrel, w.map_neg]
  have hpowe : w a ^ p.natDegree = w a ^ (p.natDegree - 1) * w a := by
    conv_lhs => rw [show p.natDegree = (p.natDegree - 1) + 1 by omega]
    rw [pow_succ]
  rw [← hwrel, hpowe] at h
  have hpow : 0 < w a ^ (p.natDegree - 1) := pow_pos (lt_trans zero_lt_one hr1) _
  nlinarith [mul_lt_mul_of_pos_right hr hpow]
/-- The ultrametric inequality bounds roots by their coefficients and one. -/
theorem apply_root_le_of_isNonarchimedean {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ)
    (hw : IsNonarchimedean w) {p : Polynomial K} (hp : p.Monic)
    {a : L} (ha : Polynomial.aeval a p = 0) {M : ℝ} (hM : 1 ≤ M)
    (hcoeff : ∀ i < p.natDegree, w (algebraMap K L (p.coeff i)) ≤ M) :
    w a ≤ M := by
  have hm : 0 < p.natDegree := Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero hp ha
  have h := apply_root_le_of_sum_bound w hp ha (A := 1) le_rfl hM hcoeff
  simp only [one_mul] at h
  apply h
  intro f B _ hB
  exact (hw.apply_sum_le_sup (Finset.nonempty_range_iff.mpr hm.ne')).trans
    (Finset.sup'_le _ _ hB)
/-- A powered complex absolute value gives the archimedean degree factor. -/
theorem apply_root_le_of_complex_embedding {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ)
    (σ : L →+* ℂ) {s : ℝ} (hs : 0 ≤ s) (hσ : ∀ a : L, w a = ‖σ a‖ ^ s)
    {p : Polynomial K} (hp : p.Monic)
    {a : L} (ha : Polynomial.aeval a p = 0) {M : ℝ} (hM : 1 ≤ M)
    (hcoeff : ∀ i < p.natDegree, w (algebraMap K L (p.coeff i)) ≤ M) :
    w a ≤ (p.natDegree : ℝ) ^ s * M := by
  have hm : 0 < p.natDegree := Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero hp ha
  apply apply_root_le_of_sum_bound w hp ha
    (Real.one_le_rpow (by exact_mod_cast hm) hs) hM hcoeff
  intro f B _ hB
  simpa only [Finset.card_range] using
    sum_le_card_rpow_mul_of_complex_embedding w σ hs hσ
      (Finset.range p.natDegree) (Finset.nonempty_range_iff.mpr hm.ne') f hB

/-- The ordinary triangle inequality bounds a monic root by its degree times a coefficient bound. -/
theorem apply_root_le_degree_mul {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) {p : Polynomial K} (hp : p.Monic)
    {a : L} (ha : Polynomial.aeval a p = 0) {M : ℝ} (hM : 1 ≤ M)
    (hcoeff : ∀ i < p.natDegree, w (algebraMap K L (p.coeff i)) ≤ M) :
    w a ≤ (p.natDegree : ℝ) * M := by
  have hm : 0 < p.natDegree := Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero hp ha
  apply apply_root_le_of_sum_bound w hp ha (by exact_mod_cast hm) hM hcoeff
  intro f B _ hB
  exact (w.sum_le _ _).trans ((Finset.sum_le_sum hB).trans_eq (by simp))
/-- An extending archimedean absolute value has the same exponent and admits
its norm normalization. -/
theorem exists_normalized_extension {K L : Type*} [Field K] [Field L] [Algebra K L]
    (w : AbsoluteValue L ℝ) (hw : ¬ IsNonarchimedean (w.under K))
    {κ : ℝ} (hκ : 0 < κ) (hκ2 : (w.under K) 2 = (2 : ℝ) ^ κ) :
    ∃ (σ : L →+* ℂ) (u : AbsoluteValue L ℝ),
      (∀ a, w a = ‖σ a‖ ^ κ) ∧ ∀ a, u a = w a ^ κ⁻¹ := by
  obtain ⟨σ, s, hs, hσ⟩ := exists_complex_embedding_of_not_isNonarchimedean w
    ((isNonarchimedean_restriction_iff w).not.mp hw)
  have htwo : (2 : ℝ) ^ s = 2 ^ κ := by
    calc
      (2 : ℝ) ^ s = w (2 : L) := by simpa only [map_ofNat, Complex.norm_ofNat] using (hσ 2).symm
      _ = (w.under K) 2 := by
        simp [under_def, map_ofNat]
      _ = _ := hκ2
  have hsk : s = κ := (Real.rpow_right_inj (by norm_num) (by norm_num)).mp htwo
  subst s
  refine ⟨σ, (NormedField.toAbsoluteValue ℂ).comp σ.injective, hσ, ?_⟩
  intro a
  rw [hσ, Real.rpow_rpow_inv (norm_nonneg _) hκ.ne']
  rfl

end AbsoluteValue

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.ExternalResults.Ostrowski
import ArakelovGeometry.ExternalResults.AbsoluteValue
import Mathlib.Analysis.RCLike.Basic

/-!
# Usual normalization on Archimedean completions

A norm-preserving field identification with the real or complex field gives
an `RCLike` structure compatible with the existing norm. For a complete field,
the intrinsic condition `‖2‖ = 2` fixes the exponent in the Archimedean
classification and therefore gives this usual normalization.
-/

noncomputable section

namespace ArakelovGeometry

open scoped ComplexOrder

@[instance_reducible]
private def rclikeOfRingEquiv {k l : Type*} [NormedField k] [CompleteSpace k] [RCLike l]
    (e : k ≃+* l) (he : ∀ x, ‖e x‖ = ‖x‖) : RCLike k := by
  classical
  let f : ℝ →+* k := e.symm.toRingHom.comp (algebraMap ℝ l)
  let a : Algebra ℝ k := f.toAlgebra
  let := a
  let na : NormedAlgebra ℝ k := {
    norm_smul_le := fun r x => by
      rw [← he (r • x), Algebra.smul_def, map_mul]
      change ‖e (e.symm ((algebraMap ℝ l) r)) * e x‖ ≤ ‖r‖ * ‖x‖
      simp only [e.apply_symm_apply, norm_mul, RCLike.norm_ofReal, he, Real.norm_eq_abs]
      exact le_rfl }
  let sr : StarRing k := {
    star := fun x => e.symm (star (e x))
    star_involutive := fun x => by simp
    star_mul := fun x y => by simp [mul_comm]
    star_add := fun x y => by simp }
  let := sr
  refine {
    toNormedField := inferInstance
    lt_norm_lt := fun x y hx hxy => ?_
    toStarRing := sr
    toNormedAlgebra := na
    toCompleteSpace := inferInstance
    re := RCLike.re.comp e.toAddMonoidHom
    im := RCLike.im.comp e.toAddMonoidHom
    I := e.symm RCLike.I
    I_re_ax := by simp
    I_mul_I_ax := ?_
    re_add_im_ax := ?_
    ofReal_re_ax := by
      intro r
      change RCLike.re (e (e.symm ((algebraMap ℝ l) r))) = r
      simp
    ofReal_im_ax := by
      intro r
      change RCLike.im (e (e.symm ((algebraMap ℝ l) r))) = 0
      simp
    mul_re_ax := by
      intro x y
      change RCLike.re (e (x * y)) =
        RCLike.re (e x) * RCLike.re (e y) - RCLike.im (e x) * RCLike.im (e y)
      simpa only [map_mul] using RCLike.mul_re (e x) (e y)
    mul_im_ax := by
      intro x y
      change RCLike.im (e (x * y)) =
        RCLike.re (e x) * RCLike.im (e y) + RCLike.im (e x) * RCLike.re (e y)
      simpa only [map_mul] using RCLike.mul_im (e x) (e y)
    conj_re_ax := by
      intro x
      change RCLike.re (e (e.symm (star (e x)))) = RCLike.re (e x)
      simp
    conj_im_ax := by
      intro x
      change RCLike.im (e (e.symm (star (e x)))) = -RCLike.im (e x)
      simp
    conj_I_ax := ?_
    norm_sq_eq_def_ax := ?_
    mul_im_I_ax := by
      intro x
      change RCLike.im (e x) * RCLike.im (e (e.symm RCLike.I)) = RCLike.im (e x)
      rw [e.apply_symm_apply]
      exact RCLike.mul_im_I_ax (e x)
    toPartialOrder := PartialOrder.lift e e.injective
    le_iff_re_im := by intros; exact RCLike.le_iff_re_im
    toDecidableEq := Classical.decEq _ }
  · obtain ⟨z, hz⟩ := DenselyNormedField.lt_norm_lt x y hx hxy (α := l)
    exact ⟨e.symm z, by simpa only [← he (e.symm z), e.apply_symm_apply] using hz⟩
  · rcases (RCLike.I_mul_I_ax (K := l)) with h | h
    · left; simpa using congrArg e.symm h
    · right; simpa only [map_mul, map_neg, map_one] using congrArg e.symm h
  · intro x
    change e.symm ((algebraMap ℝ l) (RCLike.re (e x))) +
      e.symm ((algebraMap ℝ l) (RCLike.im (e x))) * e.symm RCLike.I = x
    apply e.injective
    simpa only [map_add, map_mul, e.apply_symm_apply] using RCLike.re_add_im (e x)
  · change e.symm (star (e (e.symm RCLike.I))) = -(e.symm RCLike.I)
    simp
  · intro x
    change ‖x‖ ^ 2 = RCLike.re (e x) * RCLike.re (e x) +
      RCLike.im (e x) * RCLike.im (e x)
    simpa only [he] using (RCLike.norm_sq_eq_def (z := e x))

/-- A usual real or complex identification preserves the actual normed-field
structure, rather than replacing its norm by an equivalent one. -/
theorem isRCLikeNormedField_of_ringEquiv_norm_eq {k l : Type*}
    [NormedField k] [CompleteSpace k] [RCLike l]
    (e : k ≃+* l) (he : ∀ x, ‖e x‖ = ‖x‖) : IsRCLikeNormedField k :=
  ⟨rclikeOfRingEquiv e he, rfl⟩

private theorem cauSeqIsCompleteNorm {k : Type*} [NormedField k] [CompleteSpace k] :
    CauSeq.IsComplete k norm := by
  refine ⟨fun f => ?_⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete f.cauchySeq
  refine ⟨x, ?_⟩
  rw [Metric.tendsto_atTop] at hx
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  exact ⟨N, fun j hj => by simpa [dist_eq_norm] using hN j hj⟩

/-- The intrinsic normalization `‖2‖ = 2` characterizes the usual real or
complex norm on a complete normed field. -/
theorem isRCLikeNormedField_of_norm_two {k : Type*} [NormedField k] [CompleteSpace k]
    (h₂ : ‖(2 : k)‖ = 2) : IsRCLikeNormedField k := by
  let v := NormedField.toAbsoluteValue k
  have hna : ¬IsNonarchimedean v := by
    intro h
    have hh := h (1 : k) 1
    change ‖(1 + 1 : k)‖ ≤ max ‖(1 : k)‖ ‖(1 : k)‖ at hh
    norm_num only [one_add_one_eq_two, h₂, norm_one, max_self] at hh
  have hc : CauSeq.IsComplete k (v : k → ℝ) := by
    change CauSeq.IsComplete k norm
    exact cauSeqIsCompleteNorm
  rcases AbsoluteValue.exists_ringEquiv_real_or_complex_of_complete v hna hc with
    ⟨e, s, hs, he⟩ | ⟨e, s, hs, he⟩
  · have hpow : (2 : ℝ) ^ s = 2 := by
      have hh := he (2 : k)
      change ‖(2 : k)‖ = ‖e (2 : k)‖ ^ s at hh
      simpa only [h₂, map_ofNat, Real.norm_ofNat] using hh.symm
    have hs₁ : s = 1 := (Real.rpow_right_inj (x := 2) (by norm_num) (by norm_num)).mp
      (by simpa only [Real.rpow_one] using hpow)
    apply isRCLikeNormedField_of_ringEquiv_norm_eq e
    intro x
    have hh := he x
    change ‖x‖ = ‖e x‖ ^ s at hh
    simpa only [hs₁, Real.rpow_one] using hh.symm
  · have hpow : (2 : ℝ) ^ s = 2 := by
      have hh := he (2 : k)
      change ‖(2 : k)‖ = ‖e (2 : k)‖ ^ s at hh
      simpa only [h₂, map_ofNat, Complex.norm_ofNat] using hh.symm
    have hs₁ : s = 1 := (Real.rpow_right_inj (x := 2) (by norm_num) (by norm_num)).mp
      (by simpa only [Real.rpow_one] using hpow)
    apply isRCLikeNormedField_of_ringEquiv_norm_eq e
    intro x
    have hh := he x
    change ‖x‖ = ‖e x‖ ^ s at hh
    simpa only [hs₁, Real.rpow_one] using hh.symm

/-- A complete normed extension of a field with its usual real or complex
norm also has its usual real or complex norm. -/
theorem isRCLikeNormedField_of_normedAlgebra (k l : Type*) [NormedField k]
    [NormedField l] [NormedAlgebra k l] [IsRCLikeNormedField k] [CompleteSpace l] :
    IsRCLikeNormedField l := by
  let := IsRCLikeNormedField.rclike k
  apply isRCLikeNormedField_of_norm_two
  have hn := norm_algebraMap' l (2 : k)
  simpa only [map_ofNat, RCLike.norm_ofNat] using hn

end ArakelovGeometry

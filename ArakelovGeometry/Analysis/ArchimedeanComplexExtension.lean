/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.NormalizedCompletion
import ArakelovGeometry.Analysis.ScalarExtensionRetraction
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Actual extension of normalized complex fields

A square root of minus one excludes the real Archimedean case. The canonical
map to a complete normed extension is consequently onto, and projective scalar
extension preserves every actual isometric embedding on every tensor.
-/

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

private theorem isAlgClosed_of_rclike_sqrt_neg_one {k : Type*} [RCLike k]
    (hi : ∃ a : k, a ^ 2 = -1) : IsAlgClosed k := by
  have hI : RCLike.im (RCLike.I : k) = 1 := by
    rcases RCLike.I_eq_zero_or_im_I_eq_one (K := k) with h | h
    · obtain ⟨a, ha⟩ := hi
      let e := RCLike.realRingEquiv h
      have hr : (e a) ^ 2 = -(1 : ℝ) := by
        simpa only [map_pow, map_neg, map_one] using congrArg e ha
      nlinarith [sq_nonneg (e a)]
    · exact h
  let e := RCLike.complexRingEquiv hI
  refine ⟨fun p => ?_⟩
  have hs := (IsAlgClosed.splits (p.map e.toRingHom)).map e.symm.toRingHom
  have hc : e.symm.toRingHom.comp e.toRingHom = RingHom.id k := by
    ext x
    simp
  simpa only [Polynomial.map_map, hc, Polynomial.map_id] using hs

variable {k l : Type*} [NormedField k] [NormedField l] [NormedAlgebra k l]
  [IsRCLikeNormedField k] [CompleteSpace l]

/-- A square root of minus one makes the actual normalized Archimedean field
algebraically closed, without changing its norm or scalar operations. -/
theorem isAlgClosed_of_isRCLikeNormedField_sqrt_neg_one
    (hi : ∃ a : k, a ^ 2 = -1) : IsAlgClosed k := by
  let := IsRCLikeNormedField.rclike k
  exact isAlgClosed_of_rclike_sqrt_neg_one hi

/-- The actual scalar embedding from a normalized complex field to its
complete normed extension is bijective. -/
theorem algebraMap_bijective_of_isRCLikeNormedField_sqrt_neg_one
    (hi : ∃ a : k, a ^ 2 = -1) : Function.Bijective (algebraMap k l) := by
  let := IsRCLikeNormedField.rclike k
  let : IsRCLikeNormedField l := isRCLikeNormedField_of_normedAlgebra k l
  let := IsRCLikeNormedField.rclike l
  let : Module.Finite k l := Module.Finite.of_restrictScalars_finite ℝ k l
  let : IsAlgClosed k := isAlgClosed_of_isRCLikeNormedField_sqrt_neg_one hi
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Every actual extended tensor is rational when the normalized base field
contains a square root of minus one. -/
theorem one_tmul_surjective_of_isRCLikeNormedField_sqrt_neg_one
    (hi : ∃ a : k, a ^ 2 = -1) (V : Type*) [AddCommGroup V] [Module k V] :
    Function.Surjective (fun x : V => (1 : l) ⊗ₜ[k] x) := by
  have h := (algebraMap_bijective_of_isRCLikeNormedField_sqrt_neg_one
    (l := l) hi).surjective
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add z t hz ht =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := ht
    exact ⟨x + y, by simp only [TensorProduct.tmul_add]⟩
  | tmul a x =>
    obtain ⟨b, rfl⟩ := h a
    refine ⟨b • x, ?_⟩
    change (1 : l) ⊗ₜ[k] (b • x) = (algebraMap k l) b ⊗ₜ[k] x
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]

/-- Actual projective extension preserves every isometric embedding on all
tensors over a normalized base field containing a square root of minus one. -/
theorem scalarExtensionProjectiveSeminorm_baseChange_embedding_of_sqrt_neg_one
    (hi : ∃ a : k, a ^ 2 = -1)
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace k U]
    [NormedAddCommGroup V] [NormedSpace k V]
    (f : U →ₗ[k] V) (hf : ∀ x, ‖f x‖ = ‖x‖) (z : l ⊗[k] U) :
    scalarExtensionProjectiveSeminorm (f.baseChange l z) =
      scalarExtensionProjectiveSeminorm z := by
  obtain ⟨x, rfl⟩ := one_tmul_surjective_of_isRCLikeNormedField_sqrt_neg_one hi U z
  rw [LinearMap.baseChange_tmul,
    scalarExtensionProjectiveSeminorm_one_tmul_of_isRCLike,
    scalarExtensionProjectiveSeminorm_one_tmul_of_isRCLike]
  exact hf x

end ArakelovGeometry

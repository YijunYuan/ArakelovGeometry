/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.NonarchimedeanPowerCompletion

/-!
# Canonical algebra equivalences between actual equivalent completions

The map fixes the original field. A specified positive-power identity on the
original absolute values extends to a norm identity on every completed scalar.
-/

@[expose] public section

open Topology

noncomputable section

namespace AbsoluteValue

variable {K : Type*} [Field K]

/-- The identity of the original field extends to a canonical algebra equivalence. -/
def completionAlgEquivOfIsEquiv (v w : AbsoluteValue K ℝ) (h : v.IsEquiv w) :
    v.Completion ≃ₐ[K] w.Completion where
  toRingEquiv := UniformSpace.Completion.mapRingEquiv (WithAbs.congr v w (.refl K))
    ((isEquiv_iff_isHomeomorph v w).mp h).continuous (by
      rw [WithAbs.congr_symm]
      exact ((isEquiv_iff_isHomeomorph w v).mp h.symm).continuous)
  commutes' a := by
    change UniformSpace.Completion.mapRingHom
      (WithAbs.congr v w (.refl K)).toRingHom _
      (algebraMap K v.Completion a) = algebraMap K w.Completion a
    rw [UniformSpace.Completion.algebraMap_def,
      UniformSpace.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      WithAbs.algebraMap_right_apply]
    exact UniformSpace.Completion.mapRingHom_coe
      ((isEquiv_iff_isHomeomorph v w).mp h).continuous (WithAbs.toAbs v a)

/-- The actual completed algebra equivalence fixes every original scalar. -/
theorem completionAlgEquivOfIsEquiv_coe (v w : AbsoluteValue K ℝ) (h : v.IsEquiv w)
    (a : K) : completionAlgEquivOfIsEquiv v w h (a : v.Completion) =
      (a : w.Completion) := by
  exact UniformSpace.Completion.mapRingHom_coe
    ((isEquiv_iff_isHomeomorph v w).mp h).continuous (WithAbs.toAbs v a)

/-- The canonical completed algebra equivalence is continuous. -/
theorem continuous_completionAlgEquivOfIsEquiv (v w : AbsoluteValue K ℝ)
    (h : v.IsEquiv w) : Continuous (completionAlgEquivOfIsEquiv v w h) :=
  UniformSpace.Completion.continuous_map

/-- Its actual inverse is continuous as well. -/
theorem continuous_completionAlgEquivOfIsEquiv_symm (v w : AbsoluteValue K ℝ)
    (h : v.IsEquiv w) : Continuous (completionAlgEquivOfIsEquiv v w h).symm :=
  UniformSpace.Completion.continuous_map

/-- A specified power relation on original scalars holds on every actual completed scalar. -/
theorem norm_completionAlgEquivOfIsEquiv (v w : AbsoluteValue K ℝ) (h : v.IsEquiv w)
    (θ : ℝ) (hθ : 0 < θ) (hpow : ∀ a : K, w a = (v a) ^ θ) (z : v.Completion) :
    ‖completionAlgEquivOfIsEquiv v w h z‖ = ‖z‖ ^ θ := by
  let e := completionAlgEquivOfIsEquiv v w h
  have he : Continuous e := continuous_completionAlgEquivOfIsEquiv v w h
  change ‖e z‖ = ‖z‖ ^ θ
  refine UniformSpace.Completion.induction_on
    (p := fun z : v.Completion => ‖e z‖ = ‖z‖ ^ θ) z ?_ ?_
  · exact isClosed_eq (continuous_norm.comp he)
      (continuous_norm.rpow_const (fun _ => Or.inr hθ.le))
  · intro a
    rw [UniformSpace.Completion.norm_coe]
    change ‖completionAlgEquivOfIsEquiv v w h
      ((WithAbs.ofAbs a : K) : v.Completion)‖ = ‖a‖ ^ θ
    rw [completionAlgEquivOfIsEquiv_coe, UniformSpace.Completion.norm_coe]
    exact hpow (WithAbs.ofAbs a)

/-- The inverse completed map has the corresponding actual powered norm identity. -/
theorem norm_completionAlgEquivOfIsEquiv_symm_rpow (v w : AbsoluteValue K ℝ)
    (h : v.IsEquiv w) (θ : ℝ) (hθ : 0 < θ)
    (hpow : ∀ a : K, w a = (v a) ^ θ) (z : w.Completion) :
    ‖(completionAlgEquivOfIsEquiv v w h).symm z‖ ^ θ = ‖z‖ :=
  (norm_completionAlgEquivOfIsEquiv v w h θ hθ hpow
    ((completionAlgEquivOfIsEquiv v w h).symm z)).symm.trans
      (congrArg norm ((completionAlgEquivOfIsEquiv v w h).apply_symm_apply z))

end AbsoluteValue

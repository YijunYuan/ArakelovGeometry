/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Separable.FibreIntegral

import ArakelovGeometry.AdelicCurve.Extension.Separable.Embeddings
import ArakelovGeometry.Analysis.AbsoluteValue.Extension
import ArakelovGeometry.Analysis.AbsoluteValue.FiniteExtension
import ArakelovGeometry.Analysis.AbsoluteValue.LocalDegree
import ArakelovGeometry.MeasureTheory.Function.MonotoneClass
import Mathlib.CategoryTheory.Category.Init
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Measurability of finite separable fibre integration

Evaluation averages and monotone-class arguments establish measurable fibre
integration (Chen–Moriwaki, Theorem 3.3.4).
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u v w

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (L : Type w) [Field L] [Algebra K L]

variable [FiniteDimensional K L] [_s : Algebra.IsSeparable K L]

/-- The local-degree weighted evaluation integral is the normalized average over
embeddings into an algebraic closure, for any extension of the base absolute value. -/
theorem fibreIntegral_eval_eq_sum_embeddings (ω : AS.Ω)
    (u : AbsoluteValue (AlgebraicClosure K) ℝ) (hu : u.under K = AS.ϕ ω)
    (b : L) :
    fibreIntegral AS L (fun x ↦ x.ϕ b) ω =
      (Module.finrank K L : ℝ)⁻¹ * ∑ σ : L →ₐ[K] AlgebraicClosure K, u (σ b) := by
  classical
  let E := {w : AbsoluteValue L ℝ // w.under K = AS.ϕ ω}
  let e : ExtensionFiber AS L ω ≃ E := {
    toFun x := ⟨x.val.ϕ, x.val.restrict_eq.trans (congrArg AS.ϕ x.property)⟩
    invFun w := ⟨⟨ω, w.val, w.property⟩, rfl⟩
    left_inv x := by
      apply Subtype.ext
      exact ParameterSpaceExtension.ext AS L x.property.symm rfl
    right_inv _ := rfl }
  let : Fintype E := (AbsoluteValue.finite_extensions (L := L) (AS.ϕ ω)).fintype
  let : Fintype (ExtensionFiber AS L ω) := Fintype.ofEquiv E e.symm
  rw [fibreIntegral_eq_sum]
  simp only [fibreWeight, ENNReal.toReal_div, ENNReal.toReal_natCast]
  calc
    _ = (Module.finrank K L : ℝ)⁻¹ *
        ∑ x : ExtensionFiber AS L ω, (x.val.ϕ.localDegree K : ℝ) * x.val.ϕ b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (Module.finrank K L : ℝ)⁻¹ * ∑ w : E, (w.val.localDegree K : ℝ) * w.val b := by
      congr 1
      exact e.sum_comp (fun w ↦ (w.val.localDegree K : ℝ) * w.val b)
    _ = _ := by
      congr 1
      convert AbsoluteValue.sum_localDegree_nsmul_eq_sum_embeddings (AS.ϕ ω) u hu
        (fun w : AbsoluteValue L ℝ ↦ w b) using 1 <;> simp [nsmul_eq_mul, E]

/-- Evaluation functions have measurable fibre integrals. -/
theorem measurable_fibreIntegral_eval (b : L) :
    Measurable (fibreIntegral AS L (fun x ↦ x.ϕ b)) := by
  classical
  choose u hu using fun ω : AS.Ω ↦
    AbsoluteValue.exists_extension (L := AlgebraicClosure K) (AS.ϕ ω)
  let s (ω : AS.Ω) : ParameterSpaceExtension AS (AlgebraicClosure K) := ⟨ω, u ω, hu ω⟩
  have hs (ω : AS.Ω) : (s ω).proj = ω := rfl
  have heq (ω : AS.Ω) :
      fibreIntegral AS L (fun x ↦ x.ϕ b) ω =
        (Module.finrank K L : ℝ)⁻¹ * ∑ σ : L →ₐ[K] AlgebraicClosure K, (s ω).ϕ (σ b) :=
    fibreIntegral_eval_eq_sum_embeddings AS L ω (s ω).ϕ
      ((ϕ_restriction AS (AlgebraicClosure K) (s ω)).trans (congrArg AS.ϕ (hs ω))) b
  change Measurable fun ω ↦ fibreIntegral AS L (fun x ↦ x.ϕ b) ω
  simp_rw [heq]
  exact (measurable_sum_abv_embeddings K AS s hs b).const_mul _

/-- Finite-fibre integration preserves pointwise sequential limits of real functions. -/
theorem tendsto_fibreIntegral (f : ℕ → ParameterSpaceExtension AS L → ℝ)
    (g : ParameterSpaceExtension AS L → ℝ)
    (hf : ∀ x, Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds (g x)))
    (ω : AS.Ω) :
    Filter.Tendsto (fun n ↦ fibreIntegral AS L (f n) ω) Filter.atTop
      (nhds (fibreIntegral AS L g ω)) := by
  let : Finite (ExtensionFiber AS L ω) := finite_extensionFiber AS L ω
  let : Fintype (ExtensionFiber AS L ω) := Fintype.ofFinite _
  simp_rw [fibreIntegral_eq_sum]
  exact tendsto_finsetSum _ (fun x _ ↦ tendsto_const_nhds.mul (hf x.val))

omit _s in
/-- Nonnegative fibre integration preserves increasing sequential suprema. -/
theorem fibreLIntegral_iSup (f : ℕ → ParameterSpaceExtension AS L → ℝ≥0∞)
    (hf : Monotone f) :
    fibreLIntegral AS L (fun x ↦ ⨆ n, f n x) =
      fun ω ↦ ⨆ n, fibreLIntegral AS L (f n) ω := by
  funext ω
  let : Finite (ExtensionFiber AS L ω) := finite_extensionFiber AS L ω
  exact lintegral_iSup (fun n ↦ measurable_of_finite (fun x : ExtensionFiber AS L ω ↦ f n x.val))
    (fun n m h x ↦ hf h x.val)

omit _s in
/-- Nonnegative fibre integration preserves countable sums. -/
theorem fibreLIntegral_tsum (f : ℕ → ParameterSpaceExtension AS L → ℝ≥0∞) :
    fibreLIntegral AS L (fun x ↦ ∑' n, f n x) =
      fun ω ↦ ∑' n, fibreLIntegral AS L (f n) ω := by
  funext ω
  let : Finite (ExtensionFiber AS L ω) := finite_extensionFiber AS L ω
  exact lintegral_tsum (fun n ↦
    (measurable_of_finite (fun x : ExtensionFiber AS L ω ↦ f n x.val)).aemeasurable)

/-- Chen--Moriwaki, Theorem 3.3.4: for finite separable `L/K`, the fibre integration operator
sends measurable real-valued functions on `Ω_L` to measurable real-valued functions on `Ω_K`. -/
theorem measurable_fibreIntegral {f : ParameterSpaceExtension AS L → ℝ} (hf : Measurable f) :
    Measurable (fibreIntegral AS L f) := by
      classical
  let H : Submodule ℝ (ParameterSpaceExtension AS L → ℝ) := {
    carrier := {f | Measurable (fibreIntegral AS L f)}
    zero_mem' := by
      change Measurable fun ω : AS.Ω ↦
        ∫ _x : ExtensionFiber AS L ω, (0 : ℝ) ∂fibreProbabilityMeasure AS L ω
      simp only [integral_zero]
      exact measurable_const
    add_mem' := fun hf hg ↦ by
      change Measurable (fibreIntegral AS L (_ + _))
      rw [fibreIntegral_add]
      exact hf.add hg
    smul_mem' := fun c f hf ↦ by
      change Measurable (fibreIntegral AS L (c • f))
      rw [fibreIntegral_smul]
      exact hf.const_smul c }
  have hH : IsSeqClosed (H : Set (ParameterSpaceExtension AS L → ℝ)) := by
    intro u f hu hf
    exact measurable_of_tendsto_metrizable hu (tendsto_pi_nhds.mpr fun ω ↦
      tendsto_fibreIntegral AS L u f (fun x ↦ tendsto_pi_nhds.mp hf x) ω)
  let C : Set (ParameterSpaceExtension AS L → ℝ) :=
    Set.range (fun p : L × {φ : AS.Ω → ℝ // Measurable φ} ↦
      fun x : ParameterSpaceExtension AS L ↦ x.ϕ p.1 * p.2.val x.proj)
  have h1 : (1 : ParameterSpaceExtension AS L → ℝ) ∈ C := by
    refine ⟨⟨1, ⟨fun _ ↦ 1, measurable_const⟩⟩, ?_⟩
    ext x
    simp
  have hmul : ∀ f ∈ C, ∀ g ∈ C, f * g ∈ C := by
    rintro f ⟨⟨b, φ⟩, rfl⟩ g ⟨⟨c, ψ⟩, rfl⟩
    refine ⟨⟨b * c, ⟨φ.val * ψ.val, φ.property.mul ψ.property⟩⟩, ?_⟩
    ext x
    simp only [Pi.mul_apply, map_mul]
    ring
  have hCH : C ⊆ H := by
    rintro f ⟨⟨b, φ⟩, rfl⟩
    change Measurable (fibreIntegral AS L (fun x ↦ x.ϕ b * φ.val x.proj))
    have heq : (fun x : ParameterSpaceExtension AS L ↦ x.ϕ b * φ.val x.proj) =
        fun x ↦ φ.val x.proj * x.ϕ b := by
      ext x
      exact mul_comm _ _
    rw [heq, fibreIntegral_comp_proj_mul]
    exact φ.property.mul (measurable_fibreIntegral_eval AS L b)
  have hm : (inferInstance : MeasurableSpace (ParameterSpaceExtension AS L)) =
      ⨆ g : C, MeasurableSpace.comap g.val inferInstance := by
    rw [measurableSpace_eq_iSup_comap_eval_mul_base AS L]
    apply le_antisymm
    · apply iSup_le
      intro b
      apply iSup_le
      intro φ
      exact le_iSup_of_le ⟨_, ⟨⟨b, φ⟩, rfl⟩⟩ le_rfl
    · apply iSup_le
      intro g
      obtain ⟨⟨b, φ⟩, hg⟩ := g.property
      rw [← hg]
      exact le_iSup_of_le b (le_iSup_of_le φ le_rfl)
  apply MeasureTheory.measurable_mem_of_isSeqClosed H hH h1 hmul hCH
  exact hm ▸ hf

/-- Nonnegative measurable functions have measurable fibre integrals. -/
theorem measurable_fibreLIntegral {f : ParameterSpaceExtension AS L → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fibreLIntegral AS L f) := by
  refine Measurable.ennreal_induction
    (motive := fun f ↦ Measurable (fibreLIntegral AS L f)) ?_ ?_ ?_ hf
  · intro c s hs
    have hm := measurable_fibreIntegral AS L (measurable_const.indicator hs :
      Measurable (s.indicator fun _ : ParameterSpaceExtension AS L ↦ (1 : ℝ)))
    convert hm.ennreal_ofReal.const_mul c using 1
    funext ω
    simp only [fibreLIntegral, fibreIntegral, ← Set.indicator_comp_right, Function.comp_def]
    rw [lintegral_indicator_const (hs.preimage measurable_subtype_coe),
      integral_indicator_const _ (hs.preimage measurable_subtype_coe)]
    simp [measureReal_def]
  · intro f g _ hf hg ihf ihg
    convert ihf.add ihg using 1
    funext ω
    exact lintegral_add_left (hf.comp measurable_subtype_coe) _
  · intro f hf hmono ih
    convert Measurable.iSup ih using 1
    funext ω
    exact lintegral_iSup (fun n ↦ (hf n).comp measurable_subtype_coe)
      (fun n m h x ↦ hmono h x.val)

end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

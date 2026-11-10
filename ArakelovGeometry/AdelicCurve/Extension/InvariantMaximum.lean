/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Automorphism
public import ArakelovGeometry.AdelicCurve.Extension.FibreMaximum

/-!
# Invariant measurable fibre maxima

Consequences of Chen–Moriwaki, Propositions 3.6.1–3.6.2: taking a maximum over
an entire finite fibre is unchanged by automorphism pullback or by taking
automorphism-orbit maxima first. Its pullback is the least measurable majorant
constant on fibres. No normality or separability assumption is needed.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

open MeasureTheory

variable {K : Type*} [Field K] (AS : AdelicStructure K)
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Automorphism pullback permutes the values on each full fibre, preserving its maximum. -/
theorem fibreMaximum_comp_aut (F : ParameterSpaceExtension AS L → ℝ)
    (τ : L ≃ₐ[K] L) (ω : AS.Ω) :
    fibreMaximum AS L (F ∘ aut AS L τ) ω = fibreMaximum AS L F ω := by
  apply le_antisymm
  · apply (fibreMaximum_le_iff AS L _ ω _).mpr
    intro x
    exact le_fibreMaximum AS L F ω ⟨aut AS L τ x.val, x.property⟩
  · apply (fibreMaximum_le_iff AS L _ ω _).mpr
    intro x
    have h := le_fibreMaximum AS L (F ∘ aut AS L τ) ω
      ⟨aut AS L τ.symm x.val, x.property⟩
    simpa only [Function.comp_apply, aut_aut_symm] using h

/-- Taking automorphism-orbit maxima first leaves the maximum over a full fibre unchanged. -/
theorem fibreMaximum_orbitMaximum (F : ParameterSpaceExtension AS L → ℝ) (ω : AS.Ω) :
    fibreMaximum AS L (orbitMaximum AS L F) ω = fibreMaximum AS L F ω := by
  apply le_antisymm
  · apply (fibreMaximum_le_iff AS L _ ω _).mpr
    intro x
    apply orbitMaximum_le
    intro τ
    exact le_fibreMaximum AS L F ω ⟨aut AS L τ x.val, x.property⟩
  · apply (fibreMaximum_le_iff AS L _ ω _).mpr
    intro x
    exact (le_orbitMaximum AS L F x.val).trans
      (le_fibreMaximum AS L (orbitMaximum AS L F) ω x)

/-- A measurable function has a measurable majorant constant on every finite fibre. -/
theorem measurable_fibreMaximum_comp_proj {F : ParameterSpaceExtension AS L → ℝ}
    (hF : Measurable F) :
    Measurable (fibreMaximum AS L F ∘ proj (AS := AS) (L := L)) :=
  (measurable_fibreMaximum AS L hF).comp (measurable_proj AS L)

omit [FiniteDimensional K L] in
/-- The pullback of the fibre supremum is invariant under automorphisms. -/
theorem fibreMaximum_proj_aut (F : ParameterSpaceExtension AS L → ℝ)
    (τ : L ≃ₐ[K] L) (x : ParameterSpaceExtension AS L) :
    fibreMaximum AS L F (aut AS L τ x).proj = fibreMaximum AS L F x.proj := rfl

/-- The fibre maximum is the least base function whose pullback dominates the given function. -/
theorem fibreMaximum_le_iff_le_comp_proj (F : ParameterSpaceExtension AS L → ℝ)
    (g : AS.Ω → ℝ) :
    (∀ ω, fibreMaximum AS L F ω ≤ g ω) ↔ ∀ x, F x ≤ g x.proj := by
  constructor
  · intro h x
    exact (le_fibreMaximum AS L F x.proj ⟨x, rfl⟩).trans (h x.proj)
  · intro h ω
    apply (fibreMaximum_le_iff AS L F ω (g ω)).mpr
    intro x
    simpa only [x.property] using h x.val

end ArakelovGeometry.AdelicStructure.ParameterSpaceExtension

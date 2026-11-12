/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Line.Basic

import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction

/-!
# Subspace lattices from actual finite global balls

Finite generation is inherited from the literal global integral ball itself.
Coherence reconstructs the completed restricted ball, independently of
whether the original non-pure norm family is dominated.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]

/-- Finite generation of the literal ambient integral ball, rather than
an analytic domination premise, makes every literal subspace ball finite. -/
theorem fg_restrict_normalizedGlobalUnitBallModule_of_fg
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsUltrametric]
    (hfg : (ξ.globalUnitBallModule).FG) (F : Submodule K E) :
    ((ξ.restrict F).globalUnitBallModule (hξ := (hξ.restrict F))).FG := by
  let : Module.Finite (𝓞 K) (ξ.globalUnitBallModule) :=
    Module.Finite.iff_fg.mpr hfg
  have hfinite : Module.Finite (𝓞 K)
      ((ξ.restrict F).globalUnitBallModule (hξ := (hξ.restrict F))) :=
    Module.Finite.of_injective (ξ.restrictedGlobalUnitBallInclusion F)
      (ξ.restrictedGlobalUnitBallInclusion_injective F)
  exact Module.Finite.iff_fg.mp hfinite

variable [FiniteDimensional K E]

/-- Genuine coherence reconstructs the literal completed subspace ball
at every actual finite parameter, by its canonical integral tensor map. -/
def normalizedRestrictedGlobalCompletedTensorEquiv
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [ξ.HasFiniteNormExceptions] [hξ : ξ.IsUltrametric] (F : Submodule K E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    (normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω ⊗[𝓞 K]
      ((ξ.restrict F).globalUnitBallModule (hξ := (hξ.restrict F))) ≃ₗ[
        (normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω]
      (ξ.restrict F).completedUnitBallModule ω hω (hξ := (hξ.restrict F)) :=
  (ξ.restrict F).normalizedGlobalCompletedTensorEquivAt ω hω

@[simp]
theorem normalizedRestrictedGlobalCompletedTensorEquiv_tmul
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [ξ.HasFiniteNormExceptions] [hξ : ξ.IsUltrametric] (F : Submodule K E)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (a : (normalizedNumberFieldAdelicStructure K).completedLocalRing ω hω)
    (x : (ξ.restrict F).globalUnitBallModule (hξ := (hξ.restrict F))) :
    (ξ.normalizedRestrictedGlobalCompletedTensorEquiv F ω hω (a ⊗ₜ[𝓞 K] x) :
        ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] F) =
      (a : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion) •
        (1 ⊗ₜ[K] (x : F)) :=
  (ξ.restrict F).normalizedGlobalCompletedTensorEquivAt_tmul ω hω a x

omit [FiniteDimensional K E] in
/-- The actual finite coherent ambient lattice makes every actual line
intersection invertible without domination of the original norm family. -/
theorem normalizedRestrictedGlobalUnitBall_invertible_of_fg
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsUltrametric]
    [hfinite : ξ.HasFiniteNormExceptions] (hfg : (ξ.globalUnitBallModule).FG)
    (F : Submodule K E) (hrank : Module.finrank K F = 1) :
    Module.Invertible (𝓞 K) ((ξ.restrict F).globalUnitBallModule (hξ := (hξ.restrict F))) :=
  NumberFieldLineLattice.invertible_of_fg_of_span_eq_top_of_finrank_eq_one _
    (ξ.fg_restrict_normalizedGlobalUnitBallModule_of_fg hfg F)
    (hfinite.span_restrict_normalizedGlobalUnitBall_eq_top F) hrank

omit [FiniteDimensional K E] in
/-- A substantive bounded-index consumer of the actual finite coherent
line intersection. The element and index are produced in the original module. -/
theorem exists_normalizedRestrictedGlobalUnitBall_boundedIndex_element_of_fg
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hξ : ξ.IsUltrametric]
    [hfinite : ξ.HasFiniteNormExceptions] (hfg : (ξ.globalUnitBallModule).FG)
    (F : Submodule K E) (hrank : Module.finrank K F = 1) :
    ∃ l : (ξ.restrict F).globalUnitBallModule (hξ := (hξ.restrict F)), l ≠ 0 ∧
      Finite (((ξ.restrict F).globalUnitBallModule (hξ := (hξ.restrict F))) ⧸
        Submodule.span (𝓞 K) {l}) ∧
      Nat.card (((ξ.restrict F).globalUnitBallModule (hξ := (hξ.restrict F))) ⧸
        Submodule.span (𝓞 K) {l}) ≤ NumberFieldBoundedIndex.indexBound K := by
  let := ξ.normalizedRestrictedGlobalUnitBall_invertible_of_fg hfg F hrank
  exact NumberFieldBoundedIndex.exists_invertibleModule_boundedIndex_element K
    ((ξ.restrict F).globalUnitBallModule (hξ := (hξ.restrict F)))

end ArakelovGeometry.NormFamily

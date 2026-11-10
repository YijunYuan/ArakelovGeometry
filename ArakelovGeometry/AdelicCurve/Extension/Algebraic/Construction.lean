/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Measure
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integral
import ArakelovGeometry.Analysis.AbsoluteValue.NormalizedCompletion
import ArakelovGeometry.Analysis.AbsoluteValue.RootBounds
import Mathlib.CategoryTheory.Category.Init

/-!
# The algebraic extension adelic structure

Integrability of logarithmic evaluations, construction of the extended adelic
structure and preservation of properness in Proposition 3.4.10 and Definition 3.4.11.

The `AdelicStructure` scope provides `S ⊗[K] L` for `S.algebraicExtension L`.
This always denotes the algebraic extension construction; the finite and
finite separable constructions retain their explicit names.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure.Algebraic

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u v w

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (L : Type w) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Proposition 3.4.10: logarithmic evaluations are integrable for the projective-limit measure. -/
theorem integrable_log_measure (a : L) (ha : a ≠ 0) :
    Integrable[projectiveMeasurableSpace AS L]
      (fun x : ParameterSpaceExtension AS L ↦ Real.log ((ParameterSpaceExtension.ϕ x) a))
      (measure (AS := AS) (L := L)) := by
  let F := ofElement (K := K) L a
  let b : F := ⟨a, mem_ofElement L a⟩
  have hb : b ≠ 0 := fun h ↦ ha (congrArg Subtype.val h)
  convert integrable_comp_projFinite_measure AS L F
    (ParameterSpaceFinExtension.integrable_log AS F b hb) using 1
  funext x
  exact congrArg Real.log (congrArg (fun w : AbsoluteValue F ℝ ↦ w b)
    (ParameterSpaceFinExtension.extendAbsoluteValue_restriction (K := K) F
      ((ParameterSpaceExtension.ϕ x).under F))).symm

/-- Chen--Moriwaki, Definition 3.4.11: the concrete algebraic extension adelic structure
`S ⊗_K L`. -/
noncomputable def _root_.ArakelovGeometry.AdelicStructure.algebraicExtension :
    AdelicStructure L where
  Ω := ParameterSpaceExtension AS L
  A := projectiveMeasurableSpace AS L
  v := measure AS L
  ϕ := ParameterSpaceExtension.ϕ
  measurable_log := fun a _ha ↦ measurable_log_projective AS L a
  integrable_log := integrable_log_measure AS L

scoped[ArakelovGeometry.AdelicStructure] notation:100 S:100 " ⊗[" R "] " L:101 =>
  AdelicStructure.algebraicExtension (K := R) S L

/-- Chen--Moriwaki, Proposition 3.4.10: the algebraic extension of a proper adelic curve is
proper. -/
theorem isProper_algebraicExtension [AS.IsProper] :
    (AS ⊗[K] L).IsProper := by
  constructor
  change ∀ a : L, a ≠ 0 →
    ∫ x, Real.log (ParameterSpaceExtension.ϕ x a) ∂measure AS L = 0
  intro a ha
  let F := ofElement (K := K) L a
  let b : F := ⟨a, mem_ofElement L a⟩
  have hb : b ≠ 0 := fun h ↦ ha (congrArg Subtype.val h)
  let : (AS.finiteExtension F).IsProper :=
    ParameterSpaceFinExtension.isProper_finiteExtension AS F
  have hzero := AdelicStructure.IsProper.product_formula
    (AS := AS.finiteExtension F) b hb
  change ∫ y, Real.log (ParameterSpaceFinExtension.ϕ AS F y b)
    ∂ParameterSpaceFinExtension.measure AS F = 0 at hzero
  rw [← integral_comp_projFinite_measure AS L F
    (ParameterSpaceFinExtension.integrable_log AS F b hb)] at hzero
  convert hzero using 1
  congr 1
  funext x
  exact congrArg Real.log (congrArg (fun w : AbsoluteValue F ℝ ↦ w b)
    (ParameterSpaceFinExtension.extendAbsoluteValue_restriction (K := K) F
      ((ParameterSpaceExtension.ϕ x).under F))).symm

end ArakelovGeometry.AdelicStructure.Algebraic

namespace ArakelovGeometry.AdelicStructure

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {S : AdelicStructure K}

/-- An extending place has the same archimedean type as its base place. -/
theorem mem_Ωfin_algebraicExtension_iff (x : ParameterSpaceExtension S L) :
    x ∈ (S.algebraicExtension L).Ωfin ↔ x.base ∈ S.Ωfin := by
  change IsNonarchimedean x.abv ↔ IsNonarchimedean (S.ϕ x.base)
  rw [← x.restrict_eq]
  exact AbsoluteValue.isNonarchimedean_restriction_iff x.abv |>.symm

/-- Algebraic extension preserves the absence of archimedean places. -/
theorem forall_mem_Ωfin_algebraicExtension (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ∀ x : (S.algebraicExtension L).Ω, x ∈ (S.algebraicExtension L).Ωfin :=
  fun x ↦ (mem_Ωfin_algebraicExtension_iff x).mpr (hS x.base)

/-- Usual archimedean normalization propagates to every completed extension field. -/
theorem isRCLikeNormedField_algebraicExtension
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion := by
  intro x hx
  have hb : x.base ∈ S.Ωinf :=
    fun h ↦ hx ((mem_Ωfin_algebraicExtension_iff x).mpr h)
  have : IsRCLikeNormedField (x.abv.under K).Completion := by
    rw [x.restrict_eq]
    exact hS x.base hb
  exact isRCLikeNormedField_of_normedAlgebra (x.abv.under K).Completion x.abv.Completion

/-- Algebraic extensions of a structure with only finite places are automatically normalized. -/
theorem isRCLikeNormedField_algebraicExtension_of_forall_mem_Ωfin
    (hS : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion :=
  isRCLikeNormedField_algebraicExtension (isRCLikeNormedField_of_forall_mem_Ωfin hS)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Display the implicit base field in tensor notation when the scope is open. -/
@[scoped app_delab algebraicExtension]
meta def delabAlgebraicExtension : Delab := whenPPOption getPPNotation <|
    whenNotPPOption getPPExplicit do
  withOverApp 7 do
    let R ← withNaryArg 0 delab
    let S ← withNaryArg 2 delab
    let L ← withNaryArg 3 delab
    `($S ⊗[$R] $L)

end ArakelovGeometry.AdelicStructure

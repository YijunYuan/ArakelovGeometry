/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integral

/-!
# The algebraic extension adelic structure

Integrability of logarithmic evaluations, construction of the extended adelic
structure and preservation of properness in Proposition 3.4.10 and Definition 3.4.11.

The `AdelicStructure` scope provides `S ⊗[K] L` for `S.algebraicExtension L`.
This always denotes the algebraic extension construction; the finite and
finite separable constructions retain their explicit names.
-/

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
      ((ParameterSpaceExtension.ϕ x).restriction F))).symm

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
      ((ParameterSpaceExtension.ϕ x).restriction F))).symm

end ArakelovGeometry.AdelicStructure.Algebraic

namespace ArakelovGeometry.AdelicStructure

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

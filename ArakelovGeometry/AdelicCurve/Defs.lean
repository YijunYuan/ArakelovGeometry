/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.AbsoluteValue.Basic -- shake: keep
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.Ostrowski

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Adelic structures and adelic curves

Following Chen–Moriwaki, *Arakelov Geometry over Adelic Curves* (Springer LNM 2258),
Chapter 3, an *adelic structure* on a field `K` is a measure space `(Ω, A, v)` together with
a family `ϕ : Ω → AbsoluteValue K ℝ` of absolute values such that `ω ↦ log (ϕ ω x)` is
measurable and integrable for every nonzero `x : K`.  An *adelic curve* is a field equipped
with an adelic structure; it is *proper* when the product formula `∫ log (ϕ ω x) ∂v = 0`
holds for every nonzero `x`.

This file also defines the archimedean locus `Ωinf`, its complement `Ωfin`, and the
archimedean exponent `κ` provided by the Ostrowski-type normalization.
Properness is defined on `AdelicStructure`; `AdelicCurve.IsProper` is an abbreviation
for the same property of the underlying structure.
-/

@[expose] public section

namespace ArakelovGeometry

open MeasureTheory AbsoluteValue

universe u v

/-- An adelic structure on a field `K` (Chen–Moriwaki, §3.1): a measure space `(Ω, A, v)`
together with a family `ϕ` of absolute values on `K` such that `ω ↦ log (ϕ ω x)` is
measurable and integrable for every nonzero `x`. -/
structure AdelicStructure (K : Type u) [Field K] where
  /-- The index type of the family of absolute values. -/
  Ω : Type v
  /-- The σ-algebra on `Ω`. -/
  [A : MeasurableSpace Ω]
  /-- The measure on `Ω`. -/
  v : Measure Ω
  /-- The family of absolute values on `K`, indexed by `Ω`. -/
  ϕ : Ω → AbsoluteValue K ℝ
  /-- `ω ↦ log (ϕ ω x)` is measurable for every nonzero `x`. -/
  measurable_log : ∀ x : K, x ≠ 0 → Measurable (fun ω : Ω ↦ Real.log ((ϕ ω) x))
  /-- `ω ↦ log (ϕ ω x)` is integrable for every nonzero `x`. -/
  integrable_log : ∀ x : K, x ≠ 0 → Integrable (fun ω : Ω ↦ Real.log ((ϕ ω) x)) v

namespace AdelicStructure

instance instMeasurableSpaceΩ {K : Type*} [Field K] (AS : AdelicStructure K) :
    MeasurableSpace AS.Ω := AS.A

/-- An adelic structure is *proper* if the product formula holds for all nonzero
elements of its field (Chen–Moriwaki, §3.1). -/
class IsProper {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K) : Prop where
  /-- The product formula. -/
  product_formula : ∀ x : K, x ≠ 0 → ∫ ω, Real.log (AS.ϕ ω x) ∂AS.v = 0

/-- The nonarchimedean (finite) locus of an adelic structure. -/
def Ωfin {K : Type*} [Field K] (AS : AdelicStructure K) : Set AS.Ω :=
  {ω : AS.Ω | IsNonarchimedean (AS.ϕ ω)}

/-- The archimedean (infinite) locus of an adelic structure. -/
def Ωinf {K : Type*} [Field K] (AS : AdelicStructure K) : Set AS.Ω :=
  {ω : AS.Ω | ¬IsNonarchimedean (AS.ϕ ω)}

/-- The completed fields at infinite places carry their usual real or complex norm. -/
class IsArchimedeanNormalized {K : Type*} [Field K] (S : AdelicStructure K) : Prop where
  /-- Usual normalization at each infinite place. -/
  completion : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion

instance {K : Type*} [Field K] {S : AdelicStructure K} :
    CoeFun S.IsArchimedeanNormalized
      (fun _ ↦ ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :=
  ⟨fun h ↦ h.completion⟩

/-- Every place of the adelic structure is nonarchimedean. -/
class HasOnlyFinitePlaces {K : Type*} [Field K] (S : AdelicStructure K) : Prop where
  /-- Every index belongs to the finite locus. -/
  mem_Ωfin : ∀ ω : S.Ω, ω ∈ S.Ωfin

instance {K : Type*} [Field K] {S : AdelicStructure K} :
    CoeFun S.HasOnlyFinitePlaces (fun _ ↦ ∀ ω : S.Ω, ω ∈ S.Ωfin) :=
  ⟨fun h ↦ h.mem_Ωfin⟩

/-- Every singleton place has positive measure. -/
class HasPositiveAtoms {K : Type*} [Field K] (S : AdelicStructure K) : Prop where
  /-- Positivity of the measure of every singleton. -/
  measure_singleton_pos : ∀ ω : S.Ω, 0 < S.v {ω}

instance {K : Type*} [Field K] {S : AdelicStructure K} :
    CoeFun S.HasPositiveAtoms (fun _ ↦ ∀ ω : S.Ω, 0 < S.v {ω}) :=
  ⟨fun h ↦ h.measure_singleton_pos⟩

instance {K : Type*} [Field K] (S : AdelicStructure K) [S.HasOnlyFinitePlaces] :
    S.IsArchimedeanNormalized where
  completion ω hω := (hω (HasOnlyFinitePlaces.mem_Ωfin ω)).elim

open Classical in
/-- The archimedean exponent of a place: for `ω ∈ Ωinf`, the exponent `κ ω ∈ (0, 1]` with
`ϕ ω = |·| ^ κ ω` on `ℚ` (see `κ_def`); zero for nonarchimedean places. -/
noncomputable def κ {K : Type*} [Field K] (AS : AdelicStructure K) (ω : AS.Ω) : ℝ :=
  if hω : ω ∈ AS.Ωinf then (exists_rpow_eq_of_not_isNonarchimedean (AS.ϕ ω) hω.out).choose
  else 0

/-- The archimedean exponent lies in `[0, 1]`. -/
theorem κ_mem_Icc {K : Type*} [Field K] (AS : AdelicStructure K) (ω : AS.Ω) :
    AS.κ ω ∈ Set.Icc 0 1 := by
  by_cases hω : ω ∈ AS.Ωinf
  · unfold κ
    rw [dite_eq_left hω]
    exact Set.mem_Icc_of_Ioc
      (exists_rpow_eq_of_not_isNonarchimedean (AS.ϕ ω) hω.out).choose_spec.1
  · simp [κ, hω]

/-- The archimedean exponent vanishes exactly on the nonarchimedean locus. -/
theorem κ_eq_zero_iff {K : Type*} [Field K] (AS : AdelicStructure K) (ω : AS.Ω) :
    AS.κ ω = 0 ↔ ω ∈ AS.Ωfin := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · suffices h : ω ∉ AS.Ωinf by
      simp only [Ωinf, Set.mem_ofPred_eq, not_not, Ωfin] at *
      exact h
    by_contra hc
    unfold κ at h
    rw [dite_eq_left hc] at h
    have := (exists_rpow_eq_of_not_isNonarchimedean (AS.ϕ ω) hc.out).choose_spec.1.out.1
    linarith
  · have : ω ∉ AS.Ωinf := fun hc ↦ hc h
    simp [κ, this]

/-- On the archimedean locus, `ϕ ω` is the `κ ω`-th power of the usual absolute value
on `ℚ`. -/
theorem κ_def {K : Type*} [Field K] (AS : AdelicStructure K) {ω : AS.Ω} (hω : ω ∈ AS.Ωinf) :
    ∀ q : ℚ, AS.ϕ ω q = Rat.AbsoluteValue.real q ^ AS.κ ω := by
  have := (exists_rpow_eq_of_not_isNonarchimedean (AS.ϕ ω) hω.out).choose_spec.2
  unfold κ
  rwa [dite_eq_left hω]

end AdelicStructure

-- The universes `u`, `v` occur only jointly in the resulting sort, but they parametrize
-- genuinely independent data (the field and the index space), so we keep both.
set_option linter.checkUnivs false in
/-- An adelic curve: a field together with an adelic structure on it (Chen–Moriwaki,
§3.1). -/
structure AdelicCurve where
  /-- The underlying field. -/
  K : Type u
  /-- The field structure on `K`. -/
  [hK : Field K]
  /-- The adelic structure on `K`. -/
  AS : AdelicStructure.{u, v} K

namespace AdelicCurve

instance instFieldK {C : AdelicCurve} : Field C.K := C.hK

/-- The index space of an adelic curve. -/
abbrev Ω (C : AdelicCurve) := C.AS.Ω

/-- The measure of an adelic curve. -/
abbrev v (C : AdelicCurve) := C.AS.v

/-- The family of absolute values of an adelic curve. -/
abbrev ϕ (C : AdelicCurve) := C.AS.ϕ

/-- The archimedean exponent of an adelic curve. -/
noncomputable abbrev κ (C : AdelicCurve) := C.AS.κ

/-- The nonarchimedean locus of an adelic curve. -/
abbrev Ωfin (C : AdelicCurve) := C.AS.Ωfin

/-- The archimedean locus of an adelic curve. -/
abbrev Ωinf (C : AdelicCurve) := C.AS.Ωinf

/-- Properness of a bundled adelic curve is properness of its underlying structure. -/
abbrev IsProper (C : AdelicCurve) : Prop := C.AS.IsProper

/-- The product formula for a bundled adelic curve. -/
theorem IsProper.product_formula {C : AdelicCurve} [C.IsProper] (x : C.K) (hx : x ≠ 0) :
    ∫ ω, Real.log (C.ϕ ω x) ∂C.v = 0 :=
  AdelicStructure.IsProper.product_formula (AS := C.AS) x hx

end AdelicCurve

namespace AdelicStructure

/-- Bundle an adelic structure on `K` into an adelic curve. This is reducible so that
typeclass inference can reuse properties of the underlying structure. -/
abbrev toAdelicCurve {K : Type*} [Field K] (AS : AdelicStructure K) : AdelicCurve where
  K := K
  hK := ‹Field K›
  AS := AS

end AdelicStructure
end ArakelovGeometry

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.PositiveAtomicMeasure
import ArakelovGeometry.AdelicVectorBundle.BasisComparison
import ArakelovGeometry.AdelicCurve.Examples.FunctionFields

/-!
# Actual bidual-coordinate exceptions on a geometric atomic base

Positive singleton masses force an integrable distance to have countable
actual support. The specialization uses the genuine projective-line curve
for any constant field, including an uncountable field. Every norm equality
holds on the canonical completed fibre and on every vector in it.
-/

open MeasureTheory
open scoped TensorProduct ENNReal

noncomputable section
namespace ArakelovGeometry

namespace AdelicStructure

variable {k : Type*} [Field k]

/-- A genuine finite closed point has positive residue-degree mass. -/
theorem pointDegree_pos (v : IsDedekindDomain.HeightOneSpectrum (Polynomial k)) :
    0 < pointDegree v := by
  let g := Submodule.IsPrincipal.generator v.asIdeal
  have hg : g ≠ 0 := by
    intro h
    change Submodule.IsPrincipal.generator v.asIdeal = 0 at h
    exact v.ne_bot (by rw [← Ideal.span_singleton_generator v.asIdeal, h,
      Ideal.span_singleton_eq_bot])
  apply Nat.pos_of_ne_zero
  intro hd
  have he : g = Polynomial.C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
  have hc : g.coeff 0 ≠ 0 := by
    intro h
    exact hg (by rw [he, h, Polynomial.C_0])
  have hu : IsUnit g := he ▸ Polynomial.isUnit_C.mpr hc.isUnit
  exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
    (Submodule.IsPrincipal.generator_mem v.asIdeal) hu)

/-- The original actual geometric closed-point sigma-algebra is discrete. -/
instance discreteMeasurableSpace_functionFieldAdelicStructure :
    DiscreteMeasurableSpace (functionFieldAdelicStructure k).Ω := by
  change @DiscreteMeasurableSpace
    (Option (IsDedekindDomain.HeightOneSpectrum (Polynomial k))) ⊤
  let : MeasurableSpace (Option (IsDedekindDomain.HeightOneSpectrum (Polynomial k))) := ⊤
  exact ⟨fun _ => trivial⟩

/-- Every original geometric point has positive mass, without countability
of the constant field or of the closed-point parameter space. -/
theorem functionField_singleton_pos (x : (functionFieldAdelicStructure k).Ω) :
    0 < (functionFieldAdelicStructure k).v {x} := by
  let : MeasurableSpace (Option (IsDedekindDomain.HeightOneSpectrum (Polynomial k))) := ⊤
  cases x with
  | none =>
    change 0 < (Measure.ofSingletons (pointWeight k)) {none}
    rw [Measure.ofSingletons_singleton, pointWeight_none]
    exact zero_lt_one
  | some v =>
    change 0 < (Measure.ofSingletons (pointWeight k)) {some v}
    rw [Measure.ofSingletons_singleton, pointWeight_some]
    exact_mod_cast pointDegree_pos v

/-- Every actual geometric absolute value is non-Archimedean. -/
theorem functionField_Ωinf_eq_empty :
    (functionFieldAdelicStructure k).Ωinf = ∅ := by
  ext x
  change (¬ IsNonarchimedean (pointAbv k x)) ↔ False
  cases x with
  | none =>
    exact iff_false_intro (fun h => h (fun a b => isNonarchimedean_inftyAbvDef a b))
  | some v =>
    exact iff_false_intro (fun h => h (v.isNonarchimedean_adicAbv one_lt_expBase))

end AdelicStructure

namespace NormFamily

universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) (ξ : NormFamily S E)

/-- On an arbitrary positive-atomic discrete base, actual bidual-coordinate
distance is integrable, its actual support countable, and all completed
norms agree outside that support. The original norm need not be ultrametric. -/
theorem IsDominated.bidual_coordinate_exceptions_of_positive_atoms
    [DiscreteMeasurableSpace S.Ω] (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hfin : S.v S.Ωinf < ⊤) :
    let p := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
    let q := ofBasisMixed S E b
    Integrable (p.localDist q) S.v ∧
      (Function.support (p.localDist q)).Countable ∧
      ∀ ω ∉ Function.support (p.localDist q),
        ∀ z : (S.ϕ ω).Completion ⊗[K] E, p.norm ω z = q.norm ω z := by
  let p := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
  let q := ofBasisMixed S E b
  have hi : Integrable (p.localDist q) S.v :=
    (IsDominated.bidual_localDist_ofBasisMixed b ξ hξ hfin).integrable
      Measurable.of_discrete.aestronglyMeasurable
  refine ⟨hi, countable_support_of_integrable_of_pos_singletons hpos hi, ?_⟩
  intro ω hω z
  have hz : p.localDist q ω = 0 := Function.notMem_support.mp hω
  have he := (p.localDist_eq_zero_iff q ω).mp hz
  exact congrArg (fun n => n z) he

/-- Actual geometric bidual-coordinate exceptions over an arbitrary constant
field. This retains the genuine original completed norms and all vectors. -/
theorem IsDominated.functionField_bidual_coordinate_exceptions
    {k : Type*} [Field k] {E : Type*} [AddCommGroup E] [Module (RatFunc k) E]
    [FiniteDimensional (RatFunc k) E] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (RatFunc k) E)
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) :
    let p := ξ.dual.dual.pullback (Module.Dual.eval (RatFunc k) E)
      (Module.eval_apply_injective (RatFunc k))
    let q := ofBasisMixed (AdelicStructure.functionFieldAdelicStructure k) E b
    Integrable (p.localDist q) (AdelicStructure.functionFieldAdelicStructure k).v ∧
      (Function.support (p.localDist q)).Countable ∧
      ∀ ω ∉ Function.support (p.localDist q),
        ∀ z : ((AdelicStructure.functionFieldAdelicStructure k).ϕ ω).Completion ⊗[RatFunc k] E,
          p.norm ω z = q.norm ω z := by
  apply IsDominated.bidual_coordinate_exceptions_of_positive_atoms b ξ hξ
    AdelicStructure.functionField_singleton_pos
  rw [AdelicStructure.functionField_Ωinf_eq_empty, measure_empty]
  exact ENNReal.zero_lt_top

end NormFamily
end ArakelovGeometry

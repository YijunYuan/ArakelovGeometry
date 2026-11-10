/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.GeometricAtomicNormComparison
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Finite weighted tails of actual geometric norm distance

Finite subsets of the produced countable actual support exhaust its integral.
The original measure space need not be countable or sigma-finite. The tail
identity retains the genuine point masses and actual completed norm distance.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped TensorProduct Topology

noncomputable section
namespace ArakelovGeometry

/-- An integrable real function with countable actual support is approximated
in L1 by a finite subset of that support. The original space is arbitrary. -/
theorem exists_finset_integral_abs_compl_lt_of_countable_support
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {μ : Measure X}
    {f : X → ℝ} (hf : Integrable f μ) (hc : (Function.support f).Countable)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset X, (s : Set X) ⊆ Function.support f ∧
      (∫ x in (s : Set X)ᶜ, |f x| ∂μ) < ε := by
  classical
  let T := Function.support f
  let : Countable T := hc
  let e : T ↪ X := ⟨Subtype.val, Subtype.val_injective⟩
  let A (s : Finset T) : Set X := (s.map e : Finset X)
  have hA : ∀ s, MeasurableSet (A s) := fun s => (s.map e).measurableSet
  have hmono : Monotone A := by
    intro s t hst x hx
    obtain ⟨y, hy, he⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr ⟨y, hst hy, he⟩
  have hunion : (⋃ s, A s) = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hs
      exact y.property
    · intro hx
      exact Set.mem_iUnion.mpr ⟨{⟨x, hx⟩}, Finset.mem_map.mpr
        ⟨⟨x, hx⟩, Finset.mem_singleton_self _, rfl⟩⟩
  have hlim : Tendsto (fun s => ∫ x in A s, |f x| ∂μ) atTop
      (𝓝 (∫ x, |f x| ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone hA hmono
      (hf.abs.integrableOn : IntegrableOn (fun x => |f x|) (⋃ s, A s) μ)
    rw [hunion] at h
    have he : (∫ x in T, |f x| ∂μ) = ∫ x, |f x| ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [Function.notMem_support.mp hx, abs_zero])
    rwa [he] at h
  have htail : Tendsto (fun s => ∫ x in (A s)ᶜ, |f x| ∂μ) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : Finset T => ∫ x, |f x| ∂μ) atTop
        (𝓝 (∫ x, |f x| ∂μ)) := tendsto_const_nhds
    have h := hconst.sub hlim
    simp only [sub_self] at h
    exact h.congr (fun s => (setIntegral_compl (hA s) hf.abs).symm)
  obtain ⟨s, hs⟩ := (htail.eventually (eventually_lt_nhds hε)).exists
  refine ⟨s.map e, ?_, hs⟩
  intro x hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
  exact y.property

namespace NormFamily

universe u v w
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) (ξ : NormFamily S E)

/-- Genuine finite weighted tails of the actual pulled-bidual/coordinate
distance. No countability or sigma-finiteness of the original base is used. -/
theorem IsDominated.bidual_coordinate_finite_weighted_tail
    [DiscreteMeasurableSpace S.Ω] (hξ : ξ.IsDominated)
    (hpos : ∀ ω : S.Ω, 0 < S.v {ω}) (hfin : S.v S.Ωinf < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    let p := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
    let q := ofBasisMixed S E b
    ∃ s : Finset S.Ω, (s : Set S.Ω) ⊆ Function.support (p.localDist q) ∧
      (∫ ω in (s : Set S.Ω)ᶜ, p.localDist q ω ∂S.v) < ε ∧
      (∫ ω, p.localDist q ω ∂S.v) -
        (∑ ω ∈ s, (S.v {ω}).toReal * p.localDist q ω) < ε := by
  let p := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
  let q := ofBasisMixed S E b
  obtain ⟨hi, hc, _⟩ :=
    IsDominated.bidual_coordinate_exceptions_of_positive_atoms b ξ hξ hpos hfin
  obtain ⟨s, hs, ht⟩ :=
    exists_finset_integral_abs_compl_lt_of_countable_support hi hc hε
  have habs : (fun ω => |p.localDist q ω|) = p.localDist q :=
    funext (fun ω => abs_of_nonneg (p.localDist_nonneg q ω))
  rw [habs] at ht
  refine ⟨s, hs, ht, ?_⟩
  have he := setIntegral_compl s.measurableSet hi
  have hsum := setIntegral_finset s hi.integrableOn
  simp only [measureReal_def, smul_eq_mul] at hsum
  rw [hsum] at he
  exact he ▸ ht

/-- Genuine geometric finite tails over every constant field; the actual
closed-point masses and empty infinite locus are produced internally. -/
theorem IsDominated.functionField_bidual_coordinate_finite_weighted_tail
    {k : Type*} [Field k] {E : Type*} [AddCommGroup E] [Module (RatFunc k) E]
    [FiniteDimensional (RatFunc k) E] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (RatFunc k) E)
    (ξ : NormFamily (AdelicStructure.functionFieldAdelicStructure k) E)
    (hξ : ξ.IsDominated) {ε : ℝ} (hε : 0 < ε) :
    let S := AdelicStructure.functionFieldAdelicStructure k
    let p := ξ.dual.dual.pullback (Module.Dual.eval (RatFunc k) E)
      (Module.eval_apply_injective (RatFunc k))
    let q := ofBasisMixed S E b
    ∃ s : Finset S.Ω, (s : Set S.Ω) ⊆ Function.support (p.localDist q) ∧
      (∫ ω in (s : Set S.Ω)ᶜ, p.localDist q ω ∂S.v) < ε ∧
      (∫ ω, p.localDist q ω ∂S.v) -
        (∑ ω ∈ s, (S.v {ω}).toReal * p.localDist q ω) < ε := by
  apply IsDominated.bidual_coordinate_finite_weighted_tail b ξ hξ
    AdelicStructure.functionField_singleton_pos
  · rw [AdelicStructure.functionField_Ωinf_eq_empty, measure_empty]
    exact ENNReal.zero_lt_top
  · exact hε

end NormFamily
end ArakelovGeometry

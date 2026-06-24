import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Tactic
import Mathlib.NumberTheory.Ostrowski
import ArakelovGeometry.ExternalResults.Place
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

-- J. Neukirch, Algebraic number theory, Chapter II, Theorem 4.2
theorem Neukirch_ANT_Ch_II_Theorem_4_2 {K : Type*} [Field K] (abs : AbsoluteValue K ℝ)
  (habs : ¬ IsNonarchimedean abs) (hK : CauSeq.IsComplete K abs) :
  (
    ∃ σ : K ≃+* ℝ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s
  ) ∨ (
    ∃ σ : K ≃+* ℂ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s
  ) := by admit

theorem CauSeq.IsComplete_of_Completion {K : Type u_1} [inst : Field K]
  (abs : AbsoluteValue K ℝ) :
  let _ := abs.toNormedField;
  CauSeq.IsComplete (UniformSpace.Completion K)
  ⇑(NormedField.toAbsoluteValue (UniformSpace.Completion K)) := by
  letI := abs.toNormedField
  letI : CauSeq.IsComplete (UniformSpace.Completion K) norm := by
      refine ⟨fun f => ?_⟩
      have hf : CauchySeq (f : ℕ → UniformSpace.Completion K) := by
          rw [Metric.cauchySeq_iff]
          intro ε hε
          obtain ⟨N, hN⟩ := f.2.cauchy₂ hε
          exact ⟨N, fun m hm n hn => by simpa [dist_eq_norm] using hN m hm n hn⟩
      obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hf
      refine ⟨x, ?_⟩
      rw [Metric.tendsto_atTop] at hx
      intro ε hε
      obtain ⟨N, hN⟩ := hx ε hε
      exact ⟨N, fun j hj => by simpa [dist_eq_norm] using hN j hj⟩
  simpa only [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk] using
        (inferInstance : CauSeq.IsComplete (UniformSpace.Completion K) norm)

namespace NumberField
open AbsoluteValue

theorem ostrowski {K : Type*} [Field K] [NumberField K]
  (abs : AbsoluteValue K ℝ) (habs : abs.IsNontrivial) :
  ( ∃ v : InfinitePlace K, abs ≈ v.val ) ∨
  ( ∃ v : FinitePlace K, abs ≈ v.val) := by
  admit

open Classical in
theorem isInfinitePlace_iff' {K : Type*} [Field K] [NumberField K]
  (p : AbsoluteValue.Place K) (hp : p ≠ TrivialPlace K) :
  IsNonarchimedeanPlace p ↔
  ∃ v : FinitePlace K, p.out ≈ v.val := by
  sorry

open Classical in
theorem isFinitePlace_iff' {K : Type*} [Field K] [NumberField K]
  (p : AbsoluteValue.Place K) :
  IsArchimedeanPlace p ↔
  ∃ v : InfinitePlace K, p.out ≈ v.val := by
  sorry

instance {K : Type*} [Field K] [NumberField K] : Countable (Place K) := by
  sorry

instance {K : Type*} [Field K] [NumberField K] : Infinite (Place K) := by
  sorry

end NumberField

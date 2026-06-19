import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ArakelovGeometry.ExternalResults

-- J. Neukirch, Algebraic number theory, Chapter II, Theorem 4.2
theorem ostrowski {K : Type*} [Field K] {abs : AbsoluteValue K ℝ}
  (habs : ¬ IsNonarchimedean abs) (hK : CauSeq.IsComplete K abs) :
  (
    ∃ σ : K ≃+* ℝ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s
  ) ∨ (
    ∃ σ : K ≃+* ℂ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s
  ) := by admit

end ArakelovGeometry.ExternalResults

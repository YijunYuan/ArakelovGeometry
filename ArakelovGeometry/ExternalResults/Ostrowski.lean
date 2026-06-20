import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Tactic
import Mathlib.NumberTheory.Ostrowski

namespace ArakelovGeometry.ExternalResults

-- J. Neukirch, Algebraic number theory, Chapter II, Theorem 4.2
theorem ostrowski {K : Type*} [Field K] (abs : AbsoluteValue K ℝ)
  (habs : ¬ IsNonarchimedean abs) (hK : CauSeq.IsComplete K abs) :
  (
    ∃ σ : K ≃+* ℝ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s
  ) ∨ (
    ∃ σ : K ≃+* ℂ, ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ a : K, abs a = ‖σ a‖ ^ s
  ) := by admit

theorem completion_preserves_isNonarchimedean {K : Type*} [Field K] (abs : AbsoluteValue K ℝ) :
  letI := abs.toNormedField;
    IsNonarchimedean abs ↔
    IsNonarchimedean (UniformSpace.Completion.instNormedFieldOfCompletableTopField K
      ).toAbsoluteValue := by
  letI := abs.toNormedField
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro z w
    have hnorm := h
    change IsNonarchimedean (norm : K → ℝ) at hnorm
    refine UniformSpace.Completion.induction_on₂ z w ?_ ?_
    · change IsClosed {p : UniformSpace.Completion K × UniformSpace.Completion K |
          ‖p.1 + p.2‖ ≤ max ‖p.1‖ ‖p.2‖}
      exact isClosed_le (by fun_prop) (by fun_prop)
    · intro x y
      rw [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk]
      simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe] using
        hnorm x y
  · intro x y
    specialize h x y
    rw [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk] at h
    change ‖x + y‖ ≤ max ‖x‖ ‖y‖
    simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe] using h


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


open AbsoluteValue in
theorem charZero_of_archimedean_abs {K : Type*} [Field K] (abs : AbsoluteValue K ℝ)
  (habs : ¬ IsNonarchimedean abs) : CharZero K := by
  let Kc := Completion abs
  letI := abs.toNormedField
  replace habs : ¬ IsNonarchimedean
    (UniformSpace.Completion.instNormedFieldOfCompletableTopField K).toAbsoluteValue := by
    contrapose habs
    rwa [completion_preserves_isNonarchimedean]
  rcases ostrowski _ habs (CauSeq.IsComplete_of_Completion abs) with h1 | h2
  · rcases h1 with ⟨σ,_⟩
    have : CharZero (UniformSpace.Completion K) := by
      suffices h : CharZero ℝ by exact RingHom.charZero σ.toRingHom
      infer_instance
    exact RingHom.charZero UniformSpace.Completion.coeRingHom
  · rcases h2 with ⟨σ,_⟩
    have : CharZero (UniformSpace.Completion K) := by
      suffices h : CharZero ℂ by exact RingHom.charZero σ.toRingHom
      infer_instance
    exact RingHom.charZero UniformSpace.Completion.coeRingHom

theorem exists_s {K : Type*} [Field K] (abs : AbsoluteValue K ℝ)
  (habs : ¬ IsNonarchimedean abs) :
    ∃ s : ℝ, (s ∈ Set.Ioc 0 1 ∧
    ∀ q : ℚ, abs q = (Rat.AbsoluteValue.real q) ^ s) := by
    letI := abs.toNormedField
    have := ostrowski (UniformSpace.Completion.instNormedFieldOfCompletableTopField K
      ).toAbsoluteValue ?_ ?_
    · rcases this with h1 | h1
      · rcases h1 with ⟨σ, s, hs1, hs2⟩
        use s
        refine ⟨hs1, fun q => ?_⟩
        specialize hs2 q
        simp only [map_ratCast, Rat.norm_cast_real] at hs2
        convert hs2
        · simpa [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk] using
            (calc
              abs (q : K) = ‖((q : K) : UniformSpace.Completion K)‖ := by
                rw [UniformSpace.Completion.norm_coe]; rfl
              _ = ‖(q : UniformSpace.Completion K)‖ := by
                congr
                exact map_ratCast
                  (UniformSpace.Completion.coeRingHom : K →+* UniformSpace.Completion K) q)
        · exact List.map_inj.mp rfl
      · rcases h1 with ⟨σ, s, hs1, hs2⟩
        use s
        refine ⟨hs1, fun q => ?_⟩
        specialize hs2 q
        simp only [map_ratCast] at hs2
        convert hs2
        · simpa [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk] using
            (calc
              abs (q : K) = ‖((q : K) : UniformSpace.Completion K)‖ := by
                rw [UniformSpace.Completion.norm_coe]; rfl
              _ = ‖(q : UniformSpace.Completion K)‖ := by
                congr
                exact map_ratCast
                  (UniformSpace.Completion.coeRingHom : K →+* UniformSpace.Completion K) q)
        · simp
    · contrapose habs
      exact (completion_preserves_isNonarchimedean abs).mpr habs
    · exact CauSeq.IsComplete_of_Completion abs

end ArakelovGeometry.ExternalResults

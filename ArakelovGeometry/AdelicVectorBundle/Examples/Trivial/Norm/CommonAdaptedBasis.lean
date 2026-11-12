/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Inverse
public import ArakelovGeometry.LinearAlgebra.CommonAdaptedBasis

/-!
# Simultaneous real weights and trivial-place norms

Two arbitrary finite real filtrations admit one basis with two weight functions.
The weights are the existing intrinsic line jumps. The same basis describes the
actual trivial-place norm realizations, including the empty basis in rank zero.
-/

@[expose] public section

open Module

namespace Submodule

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

omit [FiniteDimensional K E] in
/-- An adapted basis describes every threshold by the intrinsic line jumps. -/
theorem span_basis_image_filtrationJump {ι : Type*} (b : Basis ι K E)
    {F : ℝ → Submodule K E}
    (hF : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hb : ∀ t, span K (Set.range b ∩ (F t : Set E)) = F t) (t : ℝ) :
    span K (b '' {i | t ≤ filtrationJump F (K ∙ b i)}) = F t := by
  have he : b '' {i | t ≤ filtrationJump F (K ∙ b i)} =
      Set.range b ∩ (F t : Set E) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Set.mem_range_self i,
        (mem_filtration_iff_le_jump_span hF hbot htop hleft (b i) (b.ne_zero i) t).mpr hi⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i,
        (mem_filtration_iff_le_jump_span hF hbot htop hleft (b i) (b.ne_zero i) t).mp hi,
        rfl⟩
  rw [he, hb]

/-- Two arbitrary finite real filtrations have one basis and two sets of real weights,
with simultaneous span and coordinate characterizations at every threshold.
In dimension zero the index type `Fin (finrank K E)` and both weight functions are empty. -/
theorem exists_common_weighted_basis
    {F G : ℝ → Submodule K E}
    (hF : Antitone F) (hFbot : ∃ t, F t = ⊥) (hFtop : ∃ t, F t = ⊤)
    (hFleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hG : Antitone G) (hGbot : ∃ t, G t = ⊥) (hGtop : ∃ t, G t = ⊤)
    (hGleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → G s = G t) :
    ∃ (b : Basis (Fin (finrank K E)) K E) (a c : Fin (finrank K E) → ℝ),
      (∀ t, F t = span K (b '' {i | t ≤ a i})) ∧
      (∀ t, G t = span K (b '' {i | t ≤ c i})) ∧
      (∀ t x, x ∈ F t ↔ ∀ i, b.repr x i ≠ 0 → t ≤ a i) ∧
      (∀ t x, x ∈ G t ↔ ∀ i, b.repr x i ≠ 0 → t ≤ c i) := by
  classical
  obtain ⟨b, hbF, hbG⟩ :=
    exists_basis_adapted_two_filtrations hF hFbot hFtop hG hGbot hGtop
  let a := fun i ↦ filtrationJump F (K ∙ b i)
  let c := fun i ↦ filtrationJump G (K ∙ b i)
  have hFa : ∀ t, F t = span K (b '' {i | t ≤ a i}) :=
    fun t ↦ (span_basis_image_filtrationJump b hF hFbot hFtop hFleft hbF t).symm
  have hGc : ∀ t, G t = span K (b '' {i | t ≤ c i}) :=
    fun t ↦ (span_basis_image_filtrationJump b hG hGbot hGtop hGleft hbG t).symm
  refine ⟨b, a, c, hFa, hGc, ?_, ?_⟩
  · intro t x
    rw [hFa, b.mem_span_image]
    exact ⟨fun h i hi ↦ h (Finsupp.mem_support_iff.mpr hi),
      fun h i hi ↦ h i (Finsupp.mem_support_iff.mp hi)⟩
  · intro t x
    rw [hGc, b.mem_span_image]
    exact ⟨fun h i hi ↦ h (Finsupp.mem_support_iff.mpr hi),
      fun h i hi ↦ h i (Finsupp.mem_support_iff.mp hi)⟩

end Submodule

namespace ArakelovGeometry.NormFamily

noncomputable section

open AdelicStructure
open scoped TensorProduct

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- A weighted coordinate description of all balls determines the norm on every
completed vector. The supremum of the empty coordinate support is zero. -/
theorem norm_eq_sup_of_weighted_coordinates
    (ξ : NormFamily (singleTrivialPlace K) E) [hξ : ξ.IsUltrametric]
    {ι : Type*} (b : Basis ι K E) (a : ι → ℝ)
    (hb : ∀ t x, x ∈ ξ.trivialFiltration t ↔
      ∀ i, b.repr x i ≠ 0 → t ≤ a i)
    (ω : (singleTrivialPlace K).Ω)
    (z : ((singleTrivialPlace K).ϕ ω).Completion ⊗[K] E) :
    ξ.norm ω z =
      (((b.repr (trivialCompletedTensorEquiv K E z)).support.sup fun i ↦
        ⟨Real.exp (-a i), (Real.exp_pos _).le⟩ : NNReal) : ℝ) := by
  classical
  have hn (x : E) : ξ.trivialSeminorm x =
      (((b.repr x).support.sup fun i ↦
        ⟨Real.exp (-a i), (Real.exp_pos _).le⟩ : NNReal) : ℝ) := by
    by_cases hx : x = 0
    · subst x
      rw [map_zero, map_zero, Finsupp.support_zero]
      rfl
    have hp : 0 < ξ.trivialSeminorm x := by
      rw [trivialSeminorm_apply]
      exact ξ.norm_rational_pos PUnit.unit hx
    let f : ι → NNReal := fun i ↦ ⟨Real.exp (-a i), (Real.exp_pos _).le⟩
    let M : NNReal := (b.repr x).support.sup f
    have hs : ∀ i ∈ (b.repr x).support, Real.exp (-a i) ≤ (M : ℝ) := by
      intro i hi
      exact_mod_cast (Finset.le_sup hi : f i ≤ M)
    have hrepr : b.repr x ≠ 0 := by
      intro hz
      apply hx
      apply b.repr.injective
      simpa only [map_zero] using hz
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hrepr
    have hM : 0 < (M : ℝ) := (Real.exp_pos _).trans_le (hs i hi)
    apply le_antisymm
    · have hm : x ∈ ξ.trivialFiltration (-Real.log (M : ℝ)) := by
        apply (hb _ x).mpr
        intro j hj
        have h := hs j (Finsupp.mem_support_iff.mpr hj)
        rw [← Real.exp_log hM, Real.exp_le_exp] at h
        linarith
      change ξ.trivialSeminorm x ≤ Real.exp (-(-Real.log (M : ℝ))) at hm
      simpa only [neg_neg, Real.exp_log hM] using hm
    · have hm : x ∈ ξ.trivialFiltration (-Real.log (ξ.trivialSeminorm x)) := by
        change ξ.trivialSeminorm x ≤ Real.exp (-(-Real.log (ξ.trivialSeminorm x)))
        rw [neg_neg, Real.exp_log hp]
      have hsup : M ≤ ⟨ξ.trivialSeminorm x, hp.le⟩ := by
        apply Finset.sup_le
        intro j hj
        have ha := (hb _ x).mp hm j (Finsupp.mem_support_iff.mp hj)
        change Real.exp (-a j) ≤ ξ.trivialSeminorm x
        calc
          Real.exp (-a j) ≤ Real.exp (Real.log (ξ.trivialSeminorm x)) :=
            Real.exp_le_exp.mpr (by linarith)
          _ = ξ.trivialSeminorm x := Real.exp_log hp
      exact_mod_cast hsup
  cases ω
  have he := hn (trivialCompletedTensorEquiv K E z)
  change ξ.norm PUnit.unit ((trivialCompletedTensorEquiv K E).symm
      (trivialCompletedTensorEquiv K E z)) = _ at he
  exact (congrArg (ξ.norm PUnit.unit)
    ((trivialCompletedTensorEquiv K E).symm_apply_apply z)).symm.trans he

/-- Two actual ultrametric norm families at the trivial place admit one weighted
basis describing both filtrations and both norms on all completed vectors. -/
theorem exists_common_orthogonal_basis [FiniteDimensional K E]
    (ξ η : NormFamily (singleTrivialPlace K) E)
    [hξ : ξ.IsUltrametric] [hη : η.IsUltrametric] :
    ∃ (b : Basis (Fin (finrank K E)) K E) (a c : Fin (finrank K E) → ℝ),
      (∀ t, ξ.trivialFiltration t = Submodule.span K (b '' {i | t ≤ a i})) ∧
      (∀ t, η.trivialFiltration t = Submodule.span K (b '' {i | t ≤ c i})) ∧
      (∀ ω (z : ((singleTrivialPlace K).ϕ ω).Completion ⊗[K] E),
        ξ.norm ω z =
          (((b.repr (trivialCompletedTensorEquiv K E z)).support.sup fun i ↦
            ⟨Real.exp (-a i), (Real.exp_pos _).le⟩ : NNReal) : ℝ)) ∧
      (∀ ω (z : ((singleTrivialPlace K).ϕ ω).Completion ⊗[K] E),
        η.norm ω z =
          (((b.repr (trivialCompletedTensorEquiv K E z)).support.sup fun i ↦
            ⟨Real.exp (-c i), (Real.exp_pos _).le⟩ : NNReal) : ℝ)) := by
  obtain ⟨b, a, c, hFa, hGc, hFcoord, hGcoord⟩ :=
    Submodule.exists_common_weighted_basis
      (ξ.antitone_trivialFiltration) (ξ.trivialFiltration_attains_bot_top).1
      (ξ.trivialFiltration_attains_bot_top).2 (ξ.trivialFiltration_locallyConstant_left)
      (η.antitone_trivialFiltration) (η.trivialFiltration_attains_bot_top).1
      (η.trivialFiltration_attains_bot_top).2 (η.trivialFiltration_locallyConstant_left)
  exact ⟨b, a, c, hFa, hGc, ξ.norm_eq_sup_of_weighted_coordinates b a hFcoord,
    η.norm_eq_sup_of_weighted_coordinates b c hGcoord⟩

/-- The norm realizations of two arbitrary real filtrations share an orthogonal
basis whose two weights still describe the original threshold submodules. -/
theorem exists_common_orthogonal_basis_ofTrivialFiltration [FiniteDimensional K E]
    (F G : ℝ → Submodule K E)
    (hF : Antitone F) (hFbot : ∃ t, F t = ⊥) (hFtop : ∃ t, F t = ⊤)
    (hFleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hG : Antitone G) (hGbot : ∃ t, G t = ⊥) (hGtop : ∃ t, G t = ⊤)
    (hGleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → G s = G t) :
    ∃ (b : Basis (Fin (finrank K E)) K E) (a c : Fin (finrank K E) → ℝ),
      (∀ t, F t = Submodule.span K (b '' {i | t ≤ a i})) ∧
      (∀ t, G t = Submodule.span K (b '' {i | t ≤ c i})) ∧
      (∀ ω (z : ((singleTrivialPlace K).ϕ ω).Completion ⊗[K] E),
        (ofTrivialFiltration F hF hFbot hFtop hFleft).norm ω z =
          (((b.repr (trivialCompletedTensorEquiv K E z)).support.sup fun i ↦
            ⟨Real.exp (-a i), (Real.exp_pos _).le⟩ : NNReal) : ℝ)) ∧
      (∀ ω (z : ((singleTrivialPlace K).ϕ ω).Completion ⊗[K] E),
        (ofTrivialFiltration G hG hGbot hGtop hGleft).norm ω z =
          (((b.repr (trivialCompletedTensorEquiv K E z)).support.sup fun i ↦
            ⟨Real.exp (-c i), (Real.exp_pos _).le⟩ : NNReal) : ℝ)) := by
  simpa only [trivialFiltration_ofTrivialFiltration] using
    exists_common_orthogonal_basis
      (ofTrivialFiltration F hF hFbot hFtop hFleft)
      (ofTrivialFiltration G hG hGbot hGtop hGleft)
      (hξ := (ofTrivialFiltration_isUltrametric F hF hFbot hFtop hFleft))
      (hη := (ofTrivialFiltration_isUltrametric G hG hGbot hGtop hGleft))

end

end ArakelovGeometry.NormFamily

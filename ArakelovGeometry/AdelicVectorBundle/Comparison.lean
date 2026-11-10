/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Dual
public import ArakelovGeometry.AdelicVectorBundle.Quotient
public import ArakelovGeometry.Analysis.LinearMapBound

/-!
# Comparison and local distance of norm families

Pointwise order and finite local logarithmic distance on the actual completed
fibres, as in Chen–Moriwaki, §4.1.1.9–10 (PDF pages 224–225).
The local distance is zero in dimension zero. No measurability or domination
assumption is imposed.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
variable {E : Type w} [AddCommGroup E] [Module K E]

/-- Pointwise comparison at all places and all completed-fibre vectors. -/
instance instPartialOrder : PartialOrder (NormFamily S E) where
  le ξ η := ∀ ω x, ξ.norm ω x ≤ η.norm ω x
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ ω x := (h₁ ω x).trans (h₂ ω x)
  le_antisymm _ _ h₁ h₂ := ext fun ω x ↦ le_antisymm (h₁ ω x) (h₂ ω x)

theorem le_iff {ξ η : NormFamily S E} :
    ξ ≤ η ↔ ∀ ω x, ξ.norm ω x ≤ η.norm ω x := Iff.rfl

variable (ξ η : NormFamily S E)

/-- Every pair of finite-dimensional fibre norms admits a positive comparison
constant, also when the completed scalar field has trivial absolute value. -/
theorem exists_pos_norm_le_mul [FiniteDimensional K E] (ω : S.Ω) :
    ∃ C > 0, ∀ x, η.norm ω x ≤ C * ξ.norm ω x := by
  exact @linearMap_exists_pos_bound (S.ϕ ω).Completion
    ((S.ϕ ω).Completion ⊗[K] E) ((S.ϕ ω).Completion ⊗[K] E)
    _ _ (ξ.fibreNormedAddCommGroup ω) (ξ.fibreNormedSpace ω) inferInstance
    (η.fibreNormedAddCommGroup ω).toSeminormedAddCommGroup (η.fibreNormedSpace ω)
    (LinearMap.id : (S.ϕ ω).Completion ⊗[K] E →ₗ[(S.ϕ ω).Completion]
      (S.ϕ ω).Completion ⊗[K] E)

/-- A multiplicative bound controls the difference of logarithmic norms. -/
theorem log_norm_sub_log_norm_le (ω : S.Ω) {C : ℝ} (hC : 0 < C)
    (h : ∀ x, η.norm ω x ≤ C * ξ.norm ω x)
    {x : (S.ϕ ω).Completion ⊗[K] E} (hx : x ≠ 0) :
    Real.log (η.norm ω x) - Real.log (ξ.norm ω x) ≤ Real.log C := by
  have hlog := Real.log_le_log (η.norm_pos ω hx) (h x)
  rw [Real.log_mul hC.ne' (ξ.norm_pos ω hx).ne'] at hlog
  linarith

/-- The logarithmic discrepancies on a finite-dimensional fibre are bounded. -/
theorem bddAbove_log_norm_sub [FiniteDimensional K E] (ω : S.Ω) :
    BddAbove (Set.range fun x ↦ |Real.log (ξ.norm ω x) - Real.log (η.norm ω x)|) := by
  obtain ⟨C, hC, h⟩ := ξ.exists_pos_norm_le_mul η ω
  obtain ⟨D, hD, h'⟩ := η.exists_pos_norm_le_mul ξ ω
  refine ⟨max 0 (max (Real.log C) (Real.log D)), ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hx : x = 0
  · simp only [hx, norm_zero, sub_self, abs_zero]
    exact le_max_left _ _
  · have h₁ := ξ.log_norm_sub_log_norm_le η ω hC h hx
    have h₂ := η.log_norm_sub_log_norm_le ξ ω hD h' hx
    have hC' : Real.log C ≤ max 0 (max (Real.log C) (Real.log D)) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hD' : Real.log D ≤ max 0 (max (Real.log C) (Real.log D)) :=
      (le_max_right _ _).trans (le_max_right _ _)
    exact abs_le.mpr ⟨by linarith, h₂.trans hD'⟩

/-- Local distance on the completed fibre. Including zero in the supremum adds
only the value zero and makes the zero-dimensional convention explicit. -/
noncomputable def localDist (ω : S.Ω) : ℝ :=
  sSup (Set.range fun x ↦ |Real.log (ξ.norm ω x) - Real.log (η.norm ω x)|)

variable [FiniteDimensional K E]

theorem log_norm_sub_le_localDist (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    |Real.log (ξ.norm ω x) - Real.log (η.norm ω x)| ≤ ξ.localDist η ω :=
  le_csSup (ξ.bddAbove_log_norm_sub η ω) ⟨x, rfl⟩

theorem localDist_nonneg (ω : S.Ω) : 0 ≤ ξ.localDist η ω := by
  simpa only [norm_zero, sub_self, abs_zero] using ξ.log_norm_sub_le_localDist η ω 0

omit [FiniteDimensional K E] in
/-- A bound on all logarithmic discrepancies bounds the local distance. -/
theorem localDist_le (ω : S.Ω) {D : ℝ}
    (h : ∀ x, |Real.log (ξ.norm ω x) - Real.log (η.norm ω x)| ≤ D) :
    ξ.localDist η ω ≤ D :=
  csSup_le (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact h x)

@[simp]
theorem localDist_self (ω : S.Ω) : ξ.localDist ξ ω = 0 := by
  apply le_antisymm _ (ξ.localDist_nonneg ξ ω)
  exact ξ.localDist_le ξ ω (by simp)

omit [FiniteDimensional K E] in
theorem localDist_comm (ω : S.Ω) : ξ.localDist η ω = η.localDist ξ ω := by
  simp only [localDist, abs_sub_comm]

/-- Local logarithmic distance satisfies the triangle inequality. -/
theorem localDist_triangle (ζ : NormFamily S E) (ω : S.Ω) :
    ξ.localDist ζ ω ≤ ξ.localDist η ω + η.localDist ζ ω := by
  apply ξ.localDist_le ζ ω
  intro x
  exact (abs_sub_le _ _ _).trans
    (add_le_add (ξ.log_norm_sub_le_localDist η ω x) (η.log_norm_sub_le_localDist ζ ω x))

/-- The local distance vanishes exactly when the fibre norms agree. -/
theorem localDist_eq_zero_iff (ω : S.Ω) :
    ξ.localDist η ω = 0 ↔ ξ.norm ω = η.norm ω := by
  constructor
  · intro h
    apply Seminorm.ext
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have he := ξ.log_norm_sub_le_localDist η ω x
      rw [h] at he
      have hl : Real.log (ξ.norm ω x) = Real.log (η.norm ω x) :=
        sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))
      have := congrArg Real.exp hl
      simpa only [Real.exp_log (ξ.norm_pos ω hx), Real.exp_log (η.norm_pos ω hx)] using this
  · intro h
    apply le_antisymm _ (ξ.localDist_nonneg η ω)
    apply ξ.localDist_le η ω
    simp [h]

/-- The zero-dimensional fibre has local distance zero. -/
@[simp]
theorem localDist_eq_zero_of_subsingleton [Subsingleton E] (ω : S.Ω) :
    ξ.localDist η ω = 0 := by
  rw [Subsingleton.elim η ξ]
  exact ξ.localDist_self ω

/-- The local distance is exactly the source's supremum over nonzero vectors;
the supremum of the empty real set is zero. -/
theorem localDist_eq_sSup (ω : S.Ω) :
    ξ.localDist η ω = sSup
      ((fun x ↦ |Real.log (ξ.norm ω x) - Real.log (η.norm ω x)|) '' {x | x ≠ 0}) := by
  let f := fun x ↦ |Real.log (ξ.norm ω x) - Real.log (η.norm ω x)|
  have hb : BddAbove (f '' {x | x ≠ 0}) :=
    (ξ.bddAbove_log_norm_sub η ω).mono (Set.image_subset_range _ _)
  by_cases hn : (f '' {x | x ≠ 0}).Nonempty
  · apply le_antisymm
    · apply ξ.localDist_le η ω
      intro x
      by_cases hx : x = 0
      · obtain ⟨y, hy⟩ := hn
        rcases hy with ⟨z, hz, rfl⟩
        simpa [hx] using (abs_nonneg _).trans (le_csSup hb ⟨z, hz, rfl⟩)
      · exact le_csSup hb ⟨x, hx, rfl⟩
    · apply csSup_le hn
      rintro _ ⟨x, _, rfl⟩
      exact ξ.log_norm_sub_le_localDist η ω x
  · have hz : ∀ x : (S.ϕ ω).Completion ⊗[K] E, x = 0 := by
      intro x
      by_contra hx
      exact hn ⟨f x, x, hx, rfl⟩
    rw [Set.not_nonempty_iff_eq_empty.mp hn, Real.sSup_empty]
    apply le_antisymm _ (ξ.localDist_nonneg η ω)
    apply ξ.localDist_le η ω
    intro x
    simp [hz x]

/-- Exponential comparison follows from a bound on local distance. -/
theorem norm_le_exp_mul_of_localDist_le (ω : S.Ω) {D : ℝ}
    (hD : ξ.localDist η ω ≤ D) (x : (S.ϕ ω).Completion ⊗[K] E) :
    η.norm ω x ≤ Real.exp D * ξ.norm ω x := by
  by_cases hx : x = 0
  · simp [hx]
  · have h := (abs_le.mp ((ξ.log_norm_sub_le_localDist η ω x).trans hD)).1
    have hl : Real.log (η.norm ω x) ≤ D + Real.log (ξ.norm ω x) := by linarith
    have he := Real.exp_le_exp.mpr hl
    simpa only [Real.exp_add, Real.exp_log (η.norm_pos ω hx),
      Real.exp_log (ξ.norm_pos ω hx)] using he

/-- The distance bound is equivalent to the source's two-sided multiplicative
comparison, including at zero vectors and on the zero-dimensional space. -/
theorem localDist_le_iff (ω : S.Ω) {D : ℝ} (hD : 0 ≤ D) :
    ξ.localDist η ω ≤ D ↔ ∀ x,
      Real.exp (-D) * ξ.norm ω x ≤ η.norm ω x ∧
        η.norm ω x ≤ Real.exp D * ξ.norm ω x := by
  constructor
  · intro h x
    refine ⟨?_, ξ.norm_le_exp_mul_of_localDist_le η ω h x⟩
    have hr : η.localDist ξ ω ≤ D := by rwa [localDist_comm]
    have he := mul_le_mul_of_nonneg_left
      (η.norm_le_exp_mul_of_localDist_le ξ ω hr x) (Real.exp_pos (-D)).le
    simpa [← mul_assoc, ← Real.exp_add] using he
  · intro h
    apply ξ.localDist_le η ω
    intro x
    by_cases hx : x = 0
    · simpa [hx] using hD
    · have h₁ := Real.log_le_log
        (mul_pos (Real.exp_pos (-D)) (ξ.norm_pos ω hx)) (h x).1
      have h₂ := Real.log_le_log (η.norm_pos ω hx) (h x).2
      rw [Real.log_mul (Real.exp_pos (-D)).ne' (ξ.norm_pos ω hx).ne',
        Real.log_exp] at h₁
      rw [Real.log_mul (Real.exp_pos D).ne' (ξ.norm_pos ω hx).ne',
        Real.log_exp] at h₂
      exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Exponential distortion by the local distance itself. -/
theorem norm_le_exp_localDist_mul (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    η.norm ω x ≤ Real.exp (ξ.localDist η ω) * ξ.norm ω x :=
  ξ.norm_le_exp_mul_of_localDist_le η ω le_rfl x

/-- A symmetric version of the multiplicative comparison criterion. -/
theorem localDist_le_iff_norm_le (ω : S.Ω) {D : ℝ} (hD : 0 ≤ D) :
    ξ.localDist η ω ≤ D ↔ ∀ x,
      ξ.norm ω x ≤ Real.exp D * η.norm ω x ∧
        η.norm ω x ≤ Real.exp D * ξ.norm ω x := by
  constructor
  · intro h x
    exact ⟨η.norm_le_exp_mul_of_localDist_le ξ ω (by rwa [localDist_comm]) x,
      ξ.norm_le_exp_mul_of_localDist_le η ω h x⟩
  · intro h
    apply (ξ.localDist_le_iff η ω hD).mpr
    intro x
    refine ⟨?_, (h x).2⟩
    have := mul_le_mul_of_nonneg_left (h x).1 (Real.exp_pos (-D)).le
    simpa [← mul_assoc, ← Real.exp_add] using this

/-- Duality decreases local distance on every completed fibre. -/
theorem localDist_dual_le (ω : S.Ω) :
    ξ.dual.localDist η.dual ω ≤ ξ.localDist η ω := by
  apply (ξ.dual.localDist_le_iff_norm_le η.dual ω (ξ.localDist_nonneg η ω)).mpr
  intro z
  constructor
  · apply ξ.dual_norm_le ω z
      (mul_nonneg (Real.exp_pos _).le (η.dual.norm_nonneg ω z))
    intro x
    calc
      ‖dualBaseChangeEquiv K (S.ϕ ω).Completion E z x‖ ≤
          η.dual.norm ω z * η.norm ω x := η.norm_dual_apply_le ω z x
      _ ≤ η.dual.norm ω z * (Real.exp (ξ.localDist η ω) * ξ.norm ω x) :=
        mul_le_mul_of_nonneg_left (ξ.norm_le_exp_localDist_mul η ω x)
          (η.dual.norm_nonneg ω z)
      _ = _ := by ring
  · apply η.dual_norm_le ω z
      (mul_nonneg (Real.exp_pos _).le (ξ.dual.norm_nonneg ω z))
    intro x
    calc
      ‖dualBaseChangeEquiv K (S.ϕ ω).Completion E z x‖ ≤
          ξ.dual.norm ω z * ξ.norm ω x := ξ.norm_dual_apply_le ω z x
      _ ≤ ξ.dual.norm ω z * (Real.exp (ξ.localDist η ω) * η.norm ω x) := by
        apply mul_le_mul_of_nonneg_left _ (ξ.dual.norm_nonneg ω z)
        simpa only [localDist_comm] using η.norm_le_exp_localDist_mul ξ ω x
      _ = _ := by ring

omit [FiniteDimensional K E] in
/-- Common positive rescaling leaves local distance unchanged. -/
theorem localDist_scale (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) (ω : S.Ω) :
    (ξ.scale f hf).localDist (η.scale f hf) ω = ξ.localDist η ω := by
  unfold localDist
  congr 2
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · rw [log_scale_norm _ f hf ω hx, log_scale_norm _ f hf ω hx]
    congr 1
    ring

variable {F : Type*} [AddCommGroup F] [Module K F]

/-- Pullback along an injection decreases local distance. -/
theorem localDist_pullback_le (f : F →ₗ[K] E) (hf : Function.Injective f) (ω : S.Ω) :
    (ξ.pullback f hf).localDist (η.pullback f hf) ω ≤ ξ.localDist η ω := by
  apply localDist_le
  intro x
  exact ξ.log_norm_sub_le_localDist η ω (f.baseChange (S.ϕ ω).Completion x)

/-- In particular, local distance decreases on a restricted subspace. -/
theorem localDist_restrict_le (F : Submodule K E) (ω : S.Ω) :
    (ξ.restrict F).localDist (η.restrict F) ω ≤ ξ.localDist η ω :=
  ξ.localDist_pullback_le η F.subtype F.subtype_injective ω

/-- A multiplicative comparison descends to the actual quotient norms. -/
theorem pushforward_norm_le_mul (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (ω : S.Ω) {C : ℝ} (hC : 0 < C)
    (h : ∀ x, η.norm ω x ≤ C * ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] F) :
    (η.pushforward π hπ).norm ω z ≤ C * (ξ.pushforward π hπ).norm ω z := by
  rw [mul_comm C]
  apply (div_le_iff₀ hC).mp
  apply (ξ.le_quotientSeminorm_iff π hπ ω z _).mpr
  intro x hx
  apply (div_le_iff₀ hC).mpr
  calc
    (η.pushforward π hπ).norm ω z =
        (η.pushforward π hπ).norm ω (π.baseChange (S.ϕ ω).Completion x) := by rw [hx]
    _ ≤ η.norm ω x := η.pushforward_norm_le π hπ ω x
    _ ≤ C * ξ.norm ω x := h x
    _ = ξ.norm ω x * C := mul_comm _ _

/-- Taking a quotient decreases the distance between the two norm families. -/
theorem localDist_pushforward_le (π : E →ₗ[K] F) (hπ : Function.Surjective π) (ω : S.Ω) :
    (ξ.pushforward π hπ).localDist (η.pushforward π hπ) ω ≤ ξ.localDist η ω := by
  let := Module.Finite.of_surjective π hπ
  apply ((ξ.pushforward π hπ).localDist_le_iff_norm_le (η.pushforward π hπ)
    ω (ξ.localDist_nonneg η ω)).mpr
  intro z
  constructor
  · apply η.pushforward_norm_le_mul ξ π hπ ω (Real.exp_pos _)
    intro x
    simpa only [localDist_comm] using η.norm_le_exp_localDist_mul ξ ω x
  · exact ξ.pushforward_norm_le_mul η π hπ ω (Real.exp_pos _)
      (ξ.norm_le_exp_localDist_mul η ω) z

/-- Quotient by a subspace is a contraction for local distance. -/
theorem localDist_quotient_le (F : Submodule K E) (ω : S.Ω) :
    (ξ.quotient F).localDist (η.quotient F) ω ≤ ξ.localDist η ω :=
  ξ.localDist_pushforward_le η F.mkQ F.mkQ_surjective ω

end ArakelovGeometry.NormFamily

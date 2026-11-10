/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.DeterminantDiscrepancyBound
import ArakelovGeometry.AdelicVectorBundle.DeterminantBidual

/-!
# Actual local majorant discrepancy

The infimum ranges over all actual fibre norms which majorize the given
norm and are ultrametric at a finite place, or induced by an inner product
at a normalized infinite place. Single-fibre replacement includes every
separated fibre seminorm in this range.
-/

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The elementary norm condition at one actual completed fibre. -/
def IsElementaryAt (η : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) : Prop :=
  (ω ∈ S.Ωfin → ∀ x y, η.norm ω (x + y) ≤ max (η.norm ω x) (η.norm ω y)) ∧
    ∀ hω : ω ∈ S.Ωinf,
      letI := hN ω hω
      letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
      ∃ c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E),
        ∀ x, (η.norm ω x) ^ 2 = RCLike.re (c.inner x x)

omit [FiniteDimensional K E] in
theorem IsHermitian.isElementaryAt {η : NormFamily S E}
    {hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hη : η.IsHermitian hN) (ω : S.Ω) : η.IsElementaryAt hN ω :=
  ⟨hη.1 ω, hη.2 ω⟩

/-- The actual local majorant ratios; only the chosen fibre is constrained. -/
def majorantRatios (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) : Set ℝ :=
  {a | ∃ η : NormFamily S E, η.IsElementaryAt hN ω ∧
    (∀ x, ξ.norm ω x ≤ η.norm ω x) ∧
    a = η.determinant.norm ω (1 ⊗ₜ[K] ArakelovGeometry.determinantGenerator
      (K := K) (E := E)) /
      ξ.determinant.norm ω (1 ⊗ₜ[K] ArakelovGeometry.determinantGenerator
        (K := K) (E := E))}

/-- A local elementary majorant exists on every actual completed fibre,
including rank zero. -/
theorem exists_elementaryMajorant (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) :
    ∃ η : NormFamily S E, η.IsElementaryAt hN ω ∧ ∀ x, ξ.norm ω x ≤ η.norm ω x := by
  by_cases hω : ω ∈ S.Ωinf
  · let := hN ω hω
    let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    obtain ⟨c, hc⟩ := ξ.exists_archimedean_john_innerProductCore ω
    let p := ArakelovGeometry.innerProductCoreSeminorm c
    let η := ξ.withFibreNorm ω p (ArakelovGeometry.innerProductCoreSeminorm_eq_zero_iff c)
    have hn (x : (S.ϕ ω).Completion ⊗[K] E) :
        η.norm ω x = Real.sqrt (RCLike.re (c.inner x x)) :=
      ξ.withFibreNorm_norm ω p _ x
    refine ⟨η, ⟨fun hf ↦ False.elim (hω hf), fun _ ↦ ?_⟩, fun x ↦ ?_⟩
    · exact ⟨c, fun x ↦ by rw [hn]; exact Real.sq_sqrt (c.re_inner_nonneg x)⟩
    · rw [hn]
      exact (hc x).1
  · have hf : ω ∈ S.Ωfin := not_not.mp hω
    let β := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
    let a : S.Ω → ℝ := fun _ ↦ Real.exp (ξ.localDist β ω)
    have ha : ∀ ω', 0 < a ω' := fun _ ↦ Real.exp_pos _
    let η := β.scale a ha
    have hu : η.IsUltrametric :=
      (ξ.dual.dual_isUltrametric.pullback _ _).scale a ha
    refine ⟨η, ⟨hu ω, fun hi ↦ False.elim (hi hf)⟩, fun x ↦ ?_⟩
    change ξ.norm ω x ≤ a ω * β.norm ω x
    simpa only [localDist_comm] using β.norm_le_exp_localDist_mul ξ ω x

theorem majorantRatios_nonempty (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) :
    (ξ.majorantRatios hN ω).Nonempty := by
  obtain ⟨η, he, hl⟩ := ξ.exists_elementaryMajorant hN ω
  exact ⟨_, η, he, hl, rfl⟩

theorem one_le_majorantRatio (ξ η : NormFamily S E) (ω : S.Ω)
    (hl : ∀ x, ξ.norm ω x ≤ η.norm ω x) :
    1 ≤ η.determinant.norm ω (1 ⊗ₜ[K] ArakelovGeometry.determinantGenerator
        (K := K) (E := E)) /
      ξ.determinant.norm ω (1 ⊗ₜ[K] ArakelovGeometry.determinantGenerator
        (K := K) (E := E)) := by
  apply (le_div_iff₀ (ξ.determinant.norm_rational_pos ω
    ArakelovGeometry.determinantGenerator_ne_zero)).mpr
  simpa only [one_mul] using ξ.determinant_norm_mono η ω hl _

theorem majorantRatios_bddBelow (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) :
    BddBelow (ξ.majorantRatios hN ω) := by
  refine ⟨1, ?_⟩
  rintro a ⟨η, _, hl, rfl⟩
  exact ξ.one_le_majorantRatio η ω hl

/-- The source infimum of actual local elementary majorant determinant ratios,
with its explicit empty-rank convention. -/
def majorantDiscrepancy (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) : ℝ :=
  if Module.finrank K E = 0 then 1 else sInf (ξ.majorantRatios hN ω)

theorem majorantDiscrepancy_eq_one_of_finrank_eq_zero (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) (ω : S.Ω) : ξ.majorantDiscrepancy hN ω = 1 := by
  simp only [majorantDiscrepancy, hr, ↓reduceIte]

theorem one_le_majorantDiscrepancy (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) :
    1 ≤ ξ.majorantDiscrepancy hN ω := by
  by_cases hr : Module.finrank K E = 0
  · rw [ξ.majorantDiscrepancy_eq_one_of_finrank_eq_zero hN hr]
  · rw [majorantDiscrepancy, if_neg hr]
    apply le_csInf (ξ.majorantRatios_nonempty hN ω)
    rintro a ⟨η, _, hl, rfl⟩
    exact ξ.one_le_majorantRatio η ω hl

theorem majorantDiscrepancy_le_ratio (ξ η : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω)
    (he : η.IsElementaryAt hN ω) (hl : ∀ x, ξ.norm ω x ≤ η.norm ω x) :
    ξ.majorantDiscrepancy hN ω ≤ η.determinant.norm ω
      (1 ⊗ₜ[K] ArakelovGeometry.determinantGenerator (K := K) (E := E)) /
      ξ.determinant.norm ω
        (1 ⊗ₜ[K] ArakelovGeometry.determinantGenerator (K := K) (E := E)) := by
  by_cases hr : Module.finrank K E = 0
  · rw [ξ.majorantDiscrepancy_eq_one_of_finrank_eq_zero hN hr]
    exact ξ.one_le_majorantRatio η ω hl
  · rw [majorantDiscrepancy, if_neg hr]
    exact csInf_le (ξ.majorantRatios_bddBelow hN ω) ⟨η, he, hl, rfl⟩

theorem majorantDiscrepancy_eq_one_of_elementary (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω)
    (he : ξ.IsElementaryAt hN ω) : ξ.majorantDiscrepancy hN ω = 1 := by
  apply le_antisymm _ (ξ.one_le_majorantDiscrepancy hN ω)
  have h := ξ.majorantDiscrepancy_le_ratio ξ hN ω he (fun _ ↦ le_rfl)
  simpa only [div_self (ξ.determinant.norm_rational_pos ω
    ArakelovGeometry.determinantGenerator_ne_zero).ne'] using h

/-- Every nonzero actual completed determinant vector computes the same
majorant ratio. -/
theorem determinantRatio_eq_of_nonzero (ξ η : NormFamily S E) (ω : S.Ω)
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) (hw : w ≠ 0) :
    η.determinant.norm ω w / ξ.determinant.norm ω w =
      η.determinant.norm ω (1 ⊗ₜ[K] ArakelovGeometry.determinantGenerator
        (K := K) (E := E)) /
      ξ.determinant.norm ω (1 ⊗ₜ[K] ArakelovGeometry.determinantGenerator
        (K := K) (E := E)) := by
  let w₀ := (1 : (S.ϕ ω).Completion) ⊗ₜ[K]
    ArakelovGeometry.determinantGenerator (K := K) (E := E)
  have hn : ξ.determinant.norm ω w₀ ≠ 0 :=
    (ξ.determinant.norm_rational_pos ω ArakelovGeometry.determinantGenerator_ne_zero).ne'
  have hw₀ : w₀ ≠ 0 := by
    intro he
    apply hn
    rw [he]
    exact map_zero _
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
    (show Module.finrank (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) = 1 by
      rw [Module.finrank_baseChange]; exact determinant_finrank) hw₀ w
  have ha0 : a ≠ 0 := by
    intro he
    rw [he, zero_smul] at ha
    exact hw ha.symm
  rw [← ha, η.determinant.norm_smul, ξ.determinant.norm_smul]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr ha0)

/-- The entire candidate set is independent of the chosen nonzero completed
determinant generator, so the infimum is the intrinsic source object. -/
theorem majorantRatios_eq_using_generator (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω)
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) (hw : w ≠ 0) :
    ξ.majorantRatios hN ω = {a | ∃ η : NormFamily S E, η.IsElementaryAt hN ω ∧
      (∀ x, ξ.norm ω x ≤ η.norm ω x) ∧
      a = η.determinant.norm ω w / ξ.determinant.norm ω w} := by
  ext a
  constructor
  · rintro ⟨η, he, hl, rfl⟩
    exact ⟨η, he, hl, (ξ.determinantRatio_eq_of_nonzero η ω w hw).symm⟩
  · rintro ⟨η, he, hl, rfl⟩
    exact ⟨η, he, hl, ξ.determinantRatio_eq_of_nonzero η ω w hw⟩

theorem majorantDiscrepancy_pos (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) :
    0 < ξ.majorantDiscrepancy hN ω :=
  lt_of_lt_of_le zero_lt_one (ξ.one_le_majorantDiscrepancy hN ω)

theorem log_majorantDiscrepancy_nonneg (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω) :
    0 ≤ Real.log (ξ.majorantDiscrepancy hN ω) :=
  Real.log_nonneg (ξ.one_le_majorantDiscrepancy hN ω)

theorem IsHermitian.majorantDiscrepancy_eq_one {ξ : NormFamily S E}
    {hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hξ : ξ.IsHermitian hN) (ω : S.Ω) : ξ.majorantDiscrepancy hN ω = 1 :=
  ξ.majorantDiscrepancy_eq_one_of_elementary hN ω (hξ.isElementaryAt ω)

end

end ArakelovGeometry.NormFamily

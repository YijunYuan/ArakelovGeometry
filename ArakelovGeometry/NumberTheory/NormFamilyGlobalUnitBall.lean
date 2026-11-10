/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldLocalCoefficientRingLocalization
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Literal global rational unit balls

The actual intersection of completed rational unit balls over the finite
locus, with its canonical integral action. The finite-exception hypothesis
is the genuine coherence condition in Chen–Moriwaki Proposition 4.4.2(1),
not a consequence of domination. It produces actual integral absorption
and global spanning through the proved local arithmetic absorption theorem.
-/

open scoped NumberField TensorProduct BigOperators

namespace ArakelovGeometry

universe u v w

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]

/-- The canonical actual integer action on the original vector space. -/
noncomputable instance integralVectorModule : Module (𝓞 K) E :=
  Module.compHom E (algebraMap (𝓞 K) K)

instance integralVectorScalarTower : IsScalarTower (𝓞 K) K E where
  smul_assoc a b x := by
    change (algebraMap (𝓞 K) K a * b) • x =
      algebraMap (𝓞 K) K a • (b • x)
    exact (smul_smul _ _ _).symm

@[simp]
theorem integralVector_smul (a : 𝓞 K) (x : E) :
    a • x = algebraMap (𝓞 K) K a • x := rfl

namespace NormFamily

variable {S : AdelicStructure.{u, v} K}

/-- The literal intersection of actual completed rational unit balls over
every nonarchimedean place. -/
def globalUnitBall (ξ : NormFamily S E) : Set E :=
  {x | ∀ ω ∈ S.Ωfin, x ∈ ξ.rationalUnitBall ω}

@[simp]
theorem mem_globalUnitBall (ξ : NormFamily S E) (x : E) :
    x ∈ ξ.globalUnitBall ↔ ∀ ω ∈ S.Ωfin, x ∈ ξ.rationalUnitBall ω := Iff.rfl

/-- The genuine finite-exception coherence condition in source 4.4.2(1). -/
def HasFiniteNormExceptions (ξ : NormFamily S E) : Prop :=
  ∀ x : E, {ω | ω ∈ S.Ωfin ∧
    1 < ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)}.Finite

/-- Ultrametric finite norms make the literal global ball an actual
integer-ring submodule, with the original integral scalar action. -/
def globalUnitBallModule (ξ : NormFamily S E) (hξ : ξ.IsUltrametric) :
    Submodule (𝓞 K) E where
  carrier := ξ.globalUnitBall
  zero_mem' ω _ := ξ.zero_mem_rationalUnitBall ω
  add_mem' := by
    intro x y hx hy ω hω
    change ξ.norm ω (1 ⊗ₜ[K] (x + y)) ≤ 1
    rw [TensorProduct.tmul_add]
    exact (hξ ω hω _ _).trans (max_le (hx ω hω) (hy ω hω))
  smul_mem' := by
    intro a x hx ω hω
    change ξ.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K a • x)) ≤ 1
    rw [ξ.norm_rational_smul]
    have ha := NumberField.abs_le_one_of_isIntegral hω
      (NumberField.RingOfIntegers.isIntegral_coe a)
    exact (mul_le_mul ha (hx ω hω) (ξ.norm_nonneg _ _) zero_le_one).trans_eq
      (mul_one 1)

@[simp]
theorem mem_globalUnitBallModule (ξ : NormFamily S E) (hξ : ξ.IsUltrametric) (x : E) :
    x ∈ ξ.globalUnitBallModule hξ ↔ x ∈ ξ.globalUnitBall := Iff.rfl

variable [NumberField K]

/-- Actual local absorbing scalars can be multiplied to absorb a vector
simultaneously at every place of a finite set. -/
theorem exists_integral_smul_mem_rationalUnitBall_on_finset (ξ : NormFamily S E)
    (hnt : ∀ ω ∈ S.Ωfin, (S.ϕ ω).IsNontrivial)
    (s : Finset S.Ω) (hs : ∀ ω ∈ s, ω ∈ S.Ωfin) (x : E) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ ω ∈ s,
      algebraMap (𝓞 K) K a • x ∈ ξ.rationalUnitBall ω := by
  classical
  choose a ha hball using fun ω : s =>
    ξ.exists_integral_smul_mem_rationalUnitBall ω.1 (hs ω.1 ω.2)
      (hnt ω.1 (hs ω.1 ω.2)) x
  let p := ∏ ω : s, a ω
  refine ⟨p, Finset.prod_ne_zero_iff.mpr (fun ω _ => ha ω), ?_⟩
  intro ω hω
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ (⟨ω, hω⟩ : s))
  have hprod : p = r * a ⟨ω, hω⟩ := by
    exact hr.trans (mul_comm _ _)
  have hrabs := NumberField.abs_le_one_of_isIntegral (hs ω hω)
    (NumberField.RingOfIntegers.isIntegral_coe r)
  change ξ.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K p • x)) ≤ 1
  rw [hprod, map_mul, ← smul_smul, ξ.norm_rational_smul]
  exact (mul_le_mul hrabs (hball ⟨ω, hω⟩) (ξ.norm_nonneg _ _) zero_le_one).trans_eq
    (mul_one 1)

/-- The source finite-exception condition produces a genuine nonzero
algebraic-integer scalar putting every vector in the literal global ball. -/
theorem HasFiniteNormExceptions.exists_integral_smul_mem_globalUnitBall
    {ξ : NormFamily S E} (hfinite : ξ.HasFiniteNormExceptions)
    (hnt : ∀ ω ∈ S.Ωfin, (S.ϕ ω).IsNontrivial) (x : E) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ algebraMap (𝓞 K) K a • x ∈ ξ.globalUnitBall := by
  classical
  let s := (hfinite x).toFinset
  obtain ⟨a, ha, hball⟩ := ξ.exists_integral_smul_mem_rationalUnitBall_on_finset hnt
    s (fun ω hω => ((hfinite x).mem_toFinset.mp hω).1) x
  refine ⟨a, ha, fun ω hω => ?_⟩
  by_cases hωs : ω ∈ s
  · exact hball ω hωs
  · have hx : x ∈ ξ.rationalUnitBall ω := by
      by_contra hnot
      apply hωs
      exact (hfinite x).mem_toFinset.mpr ⟨hω, not_le.mp hnot⟩
    change ξ.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K a • x)) ≤ 1
    rw [ξ.norm_rational_smul]
    have habs := NumberField.abs_le_one_of_isIntegral hω
      (NumberField.RingOfIntegers.isIntegral_coe a)
    exact (mul_le_mul habs hx (ξ.norm_nonneg _ _) zero_le_one).trans_eq (mul_one 1)

/-- Global spanning is proved from the genuine source coherence hypothesis
through actual integral absorption, without assuming it as a certificate. -/
theorem HasFiniteNormExceptions.span_globalUnitBall_eq_top
    {ξ : NormFamily S E} (hfinite : ξ.HasFiniteNormExceptions)
    (hnt : ∀ ω ∈ S.Ωfin, (S.ϕ ω).IsNontrivial) :
    Submodule.span K ξ.globalUnitBall = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha, hx⟩ := hfinite.exists_integral_smul_mem_globalUnitBall hnt x
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
  have hmem := (Submodule.span K ξ.globalUnitBall).smul_mem
    (algebraMap (𝓞 K) K a)⁻¹ (Submodule.subset_span hx)
  simpa only [smul_smul, inv_mul_cancel₀ haK, one_smul] using hmem

end NormFamily
end ArakelovGeometry

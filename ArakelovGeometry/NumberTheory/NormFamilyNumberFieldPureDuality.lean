/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldPureDual
import ArakelovGeometry.NumberTheory.NormFamilyCompletedLocalLattice

/-!
# Integral duality on actual pure completed unit balls

Exact pure rescaling identifies the literal operator-norm ball with the
integral polar of the original completed unit ball. The integral dual map
uses the canonical completed generic fibre of that same literal ball.
-/

open scoped NumberField TensorProduct
noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E]
  [Module K E] [FiniteDimensional K E]

omit [FiniteDimensional K E] in
theorem IsPureAtFinitePlaces.exists_norm_one_rescaling
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    {x : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] E}
    (hx : x ≠ 0) :
    ∃ a : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion,
      a ≠ 0 ∧ ξ.norm ω (a⁻¹ • x) = 1 ∧ a • (a⁻¹ • x) = x := by
  obtain ⟨a, ha, hn⟩ := hξ ω hω x hx
  refine ⟨a, ha, ?_, ?_⟩
  · rw [ξ.norm_smul, norm_inv, ← hn]
    exact inv_mul_cancel₀ (ξ.norm_pos ω hx).ne'
  · rw [smul_smul, mul_inv_cancel₀ ha, one_smul]

theorem IsPureAtFinitePlaces.dual_norm_le_one_iff_unitBall
    {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}
    (hξ : ξ.IsPureAtFinitePlaces)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] Module.Dual K E) :
    ξ.dual.norm ω z ≤ 1 ↔
      ∀ x, ξ.norm ω x ≤ 1 → ‖dualBaseChangeEquiv K _ E z x‖ ≤ 1 := by
  constructor
  · intro hz x hx
    exact (ξ.norm_dual_apply_le ω z x).trans
      (mul_le_one₀ hz (ξ.norm_nonneg ω x) hx)
  · intro h
    apply ξ.dual_norm_le ω z zero_le_one
    intro x
    by_cases hx : x = 0
    · simp only [hx, map_zero, _root_.norm_zero, ξ.norm_zero, mul_zero, le_refl]
    · obtain ⟨a, ha, hn, hr⟩ := hξ.exists_norm_one_rescaling ω hω hx
      have hb := h (a⁻¹ • x) hn.le
      have hna : ‖a‖ = ξ.norm ω x := by
        have hh := congrArg (ξ.norm ω) hr
        rw [ξ.norm_smul, hn, mul_one] at hh
        exact hh
      calc
        ‖dualBaseChangeEquiv K _ E z x‖ =
            ‖a‖ * ‖dualBaseChangeEquiv K _ E z (a⁻¹ • x)‖ := by
          conv_lhs => rw [← hr]
          rw [map_smul, _root_.norm_smul]
        _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hb (_root_.norm_nonneg _)
        _ = 1 * ξ.norm ω x := by rw [mul_one, one_mul, hna]

namespace CompletedPureDuality

private abbrev curve := normalizedNumberFieldAdelicStructure K

variable (ξ : NormFamily (curve (K := K)) E) (ω : (curve (K := K)).Ω)
  (hω : ω ∈ (curve (K := K)).Ωfin) (hUltra : ξ.IsUltrametric)

private abbrev fibre (ω : (curve (K := K)).Ω) := ((curve (K := K)).ϕ ω).Completion
private abbrev coeff (ω : (curve (K := K)).Ω)
    (hω : ω ∈ (curve (K := K)).Ωfin) := (curve (K := K)).completedLocalRing ω hω

local notation "F" => fibre ω
local notation "O" => coeff ω hω
local notation "U" => ξ.completedUnitBallModule ω hω hUltra
local notation "D" => ξ.dual.completedUnitBallModule ω hω ξ.dual_isUltrametric

/-- Restriction of the actual completed dual ball to the literal primal integral ball. -/
def integralDualRestriction : D →ₗ[O] Module.Dual O U where
  toFun z :=
    { toFun x := ⟨dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E)
        (x : F ⊗[K] E), ((curve (K := K)).mem_completedLocalRing ω hω _).mpr
          ((ξ.norm_dual_apply_le ω _ _).trans
            (mul_le_one₀ z.property (ξ.norm_nonneg ω _) x.property))⟩
      map_add' x y := Subtype.ext (by
        change dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E)
          ((x : F ⊗[K] E) + (y : F ⊗[K] E)) = _
        change dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E)
          ((x : F ⊗[K] E) + (y : F ⊗[K] E)) =
          dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E) (x : F ⊗[K] E) +
          dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E) (y : F ⊗[K] E)
        exact map_add _ _ _)
      map_smul' a x := Subtype.ext (by
        change dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E)
          ((a : F) • (x : F ⊗[K] E)) = (a : F) * _
        rw [map_smul, smul_eq_mul]) }
  map_add' z t := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change dualBaseChangeEquiv K F E
      ((z : F ⊗[K] Module.Dual K E) + (t : F ⊗[K] Module.Dual K E))
      (x : F ⊗[K] E) =
      dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E) (x : F ⊗[K] E) +
      dualBaseChangeEquiv K F E (t : F ⊗[K] Module.Dual K E) (x : F ⊗[K] E)
    exact LinearMap.congr_fun (map_add (dualBaseChangeEquiv K F E) _ _) _
  map_smul' a z := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change dualBaseChangeEquiv K F E
      ((a : F) • (z : F ⊗[K] Module.Dual K E)) (x : F ⊗[K] E) =
      (a : F) * dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E)
        (x : F ⊗[K] E)
    exact LinearMap.congr_fun ((dualBaseChangeEquiv K F E).map_smul (a : F)
      (z : F ⊗[K] Module.Dual K E)) (x : F ⊗[K] E)

@[simp]
theorem integralDualRestriction_apply (z : D) (x : U) :
    (integralDualRestriction ξ ω hω hUltra z x : F) =
      dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E) (x : F ⊗[K] E) := rfl

/-- Exact pure rescaling makes the literal integral restriction injective. -/
theorem integralDualRestriction_injective (hPure : ξ.IsPureAtFinitePlaces) :
    Function.Injective (integralDualRestriction ξ ω hω hUltra) := by
  intro z t h
  apply Subtype.ext
  apply (dualBaseChangeEquiv K F E).injective
  apply LinearMap.ext
  intro x
  by_cases hx : x = 0
  · simp only [hx, map_zero]
  · obtain ⟨a, ha, hn, hr⟩ := hPure.exists_norm_one_rescaling ω hω hx
    let y : U := ⟨a⁻¹ • x, hn.le⟩
    have he := congrArg (fun f : Module.Dual O U => (f y : F)) h
    change dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E) (a⁻¹ • x) =
      dualBaseChangeEquiv K F E (t : F ⊗[K] Module.Dual K E) (a⁻¹ • x) at he
    calc
      dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E) x =
          a • dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E) (a⁻¹ • x) := by
        rw [← map_smul, hr]
      _ = a • dualBaseChangeEquiv K F E (t : F ⊗[K] Module.Dual K E) (a⁻¹ • x) :=
        congrArg (fun b : F => a • b) he
      _ = dualBaseChangeEquiv K F E (t : F ⊗[K] Module.Dual K E) x := by
        rw [← map_smul, hr]

/-- Extend an actual integral functional through the canonical completed generic fibre. -/
def integralDualExtension (hnt : ((curve (K := K)).ϕ ω).IsNontrivial)
    (g : Module.Dual O U) : Module.Dual F (F ⊗[K] E) :=
  (((Algebra.linearMap O F).comp g).liftBaseChange F).comp
    (ξ.completedUnitBallGenericFibreEquiv ω hω hnt hUltra).symm.toLinearMap

@[simp]
theorem integralDualExtension_apply (hnt : ((curve (K := K)).ϕ ω).IsNontrivial)
    (g : Module.Dual O U) (x : U) :
    integralDualExtension ξ ω hω hUltra hnt g (x : F ⊗[K] E) = (g x : F) := by
  let e := ξ.completedUnitBallGenericFibreEquiv ω hω hnt hUltra
  have hs : e.symm (x : F ⊗[K] E) = (1 : F) ⊗ₜ[O] x := by
    apply e.injective
    rw [e.apply_symm_apply]
    simpa only [one_smul] using
      (ξ.completedUnitBallGenericFibreEquiv_tmul ω hω hnt hUltra 1 x).symm
  change ((Algebra.linearMap O F).comp g).liftBaseChange F
    (e.symm (x : F ⊗[K] E)) = _
  rw [hs, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

/-- Pure polar equality puts every extended integral functional in the actual dual ball. -/
theorem integralDualExtension_norm_le_one (hnt : ((curve (K := K)).ϕ ω).IsNontrivial)
    (hPure : ξ.IsPureAtFinitePlaces) (g : Module.Dual O U) :
    ξ.dual.norm ω ((dualBaseChangeEquiv K F E).symm
      (integralDualExtension ξ ω hω hUltra hnt g)) ≤ 1 := by
  apply (hPure.dual_norm_le_one_iff_unitBall ω hω _).mpr
  intro x hx
  rw [LinearEquiv.apply_symm_apply]
  have he := integralDualExtension_apply ξ ω hω hUltra hnt g (⟨x, hx⟩ : U)
  rw [he]
  exact ((curve (K := K)).mem_completedLocalRing ω hω _).mp (g ⟨x, hx⟩).property

/-- Every integral functional extends to a member of the actual completed dual ball. -/
theorem integralDualRestriction_surjective
    (hnt : ((curve (K := K)).ϕ ω).IsNontrivial) (hPure : ξ.IsPureAtFinitePlaces) :
    Function.Surjective (integralDualRestriction ξ ω hω hUltra) := by
  intro g
  let z := (dualBaseChangeEquiv K F E).symm
    (integralDualExtension ξ ω hω hUltra hnt g)
  have hz : ξ.dual.norm ω z ≤ 1 :=
    integralDualExtension_norm_le_one ξ ω hω hUltra hnt hPure g
  refine ⟨⟨z, hz⟩, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change dualBaseChangeEquiv K F E z (x : F ⊗[K] E) = (g x : F)
  dsimp only [z]
  rw [LinearEquiv.apply_symm_apply, integralDualExtension_apply]

/-- The extension and restriction retain every original completed dual vector. -/
theorem integralDualExtension_restrict
    (hnt : ((curve (K := K)).ϕ ω).IsNontrivial) (z : D) :
    integralDualExtension ξ ω hω hUltra hnt
      (integralDualRestriction ξ ω hω hUltra z) =
      dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E) := by
  apply (ξ.completedLocalUnitBallBasis ω hω hnt hUltra).ext
  intro i
  rw [ξ.completedLocalUnitBallBasis_apply,
    ← ξ.completedUnitBallBasis_coe ω hω hnt hUltra i,
    integralDualExtension_apply, integralDualRestriction_apply]

/-- The canonical actual integral-dual isomorphism is the original restriction map. -/
def integralDualEquiv (hPure : ξ.IsPureAtFinitePlaces) : D ≃ₗ[O] Module.Dual O U :=
  LinearEquiv.ofBijective (integralDualRestriction ξ ω hω hUltra)
    ⟨integralDualRestriction_injective ξ ω hω hUltra hPure,
      integralDualRestriction_surjective ξ ω hω hUltra
        (NormalizedNumberFieldPlaces.parameter_isNontrivial
          (NormalizedNumberFieldPlaces.parameterMeasurableEquivNontrivialPlace.symm ω)) hPure⟩

@[simp]
theorem integralDualEquiv_apply (hPure : ξ.IsPureAtFinitePlaces) (z : D) (x : U) :
    (integralDualEquiv ξ ω hω hUltra hPure z x : F) =
      dualBaseChangeEquiv K F E (z : F ⊗[K] Module.Dual K E) (x : F ⊗[K] E) := rfl

end CompletedPureDuality

end ArakelovGeometry.NormFamily

/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.GenericFibre
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Purity.Model

import Mathlib.Topology.Sheaves.Init

/-! # Integer bases of actual full number-field lattices

The literal integral submodule is finite free over `ℤ`, and its canonical
rational tensor is the original space with the canonical restricted action.
The exact integer rank and bases are derived, including rank zero. No freeness
over the number-field integer ring is assumed.
-/

@[expose] public section

open NumberField
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldFullLattice

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]

theorem finite_integer (M : Submodule (𝓞 K) E) (hfg : M.FG) : Module.Finite ℤ M := by
  let : Module.Finite (𝓞 K) M := Module.Finite.of_fg hfg
  exact Module.Finite.trans (𝓞 K) M

theorem isTorsionFree_integer (M : Submodule (𝓞 K) E) : Module.IsTorsionFree ℤ M := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a x h
  have hz : a • (x : E) = 0 := congrArg Subtype.val h
  have hzK : (a : K) • (x : E) = 0 := (Int.cast_smul_eq_zsmul K a (x : E)).trans hz
  rcases smul_eq_zero.mp hzK with ha | hx
  · exact Or.inl (Int.cast_eq_zero.mp ha)
  · exact Or.inr (Subtype.ext hx)

theorem free_integer (M : Submodule (𝓞 K) E) (hfg : M.FG) : Module.Free ℤ M := by
  let := finite_integer M hfg
  let := isTorsionFree_integer M
  infer_instance

def integerBasis (M : Submodule (𝓞 K) E) (hfg : M.FG) :
    Module.Basis (Fin (Module.finrank ℤ M)) ℤ M := by
  let := finite_integer M hfg
  let := free_integer M hfg
  exact Module.finBasis ℤ M

/-- The canonical restricted rational action is fixed in the result type. -/
def rationalTensorEquiv (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
    ℚ ⊗[ℤ] M ≃ₗ[ℚ] E := by
  letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  letI : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  let := NormFamily.integerRing_rationalIsPushout (K := K)
  exact (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 K) K M).symm.trans
    ((genericTensorEquiv M hspan).restrictScalars ℚ)

@[simp]
theorem rationalTensorEquiv_tmul (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) (q : ℚ) (x : M) :
    rationalTensorEquiv M hspan (q ⊗ₜ[ℤ] x) = algebraMap ℚ K q • (x : E) := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  let : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  let := NormFamily.integerRing_rationalIsPushout (K := K)
  change genericTensorEquiv M hspan
    ((Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 K) K M).symm (q ⊗ₜ[ℤ] x)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, genericTensorEquiv_tmul]

def integerRationalBasis (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
    Module.Basis (Fin (Module.finrank ℤ M)) ℚ E := by
  letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  exact ((integerBasis M hfg).baseChange ℚ).map (rationalTensorEquiv M hspan)

@[simp]
theorem integerRationalBasis_coe (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (i : Fin (Module.finrank ℤ M)) :
    integerRationalBasis M hfg hspan i = (integerBasis M hfg i : E) := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  rw [integerRationalBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    rationalTensorEquiv_tmul, map_one, one_smul]

variable [FiniteDimensional K E]

theorem finrank_integer (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    Module.finrank ℤ M = Module.finrank ℚ K * Module.finrank K E := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  let : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  have hb := Module.finrank_eq_card_basis (integerRationalBasis M hfg hspan)
  rw [Fintype.card_fin] at hb
  exact hb.symm.trans (Module.finrank_mul_finrank ℚ K E).symm

def integralBasis (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    Module.Basis (Fin (Module.finrank ℚ K * Module.finrank K E)) ℤ M :=
  (integerBasis M hfg).reindex (finCongr (finrank_integer M hfg hspan))

def integralRationalBasis (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
    Module.Basis (Fin (Module.finrank ℚ K * Module.finrank K E)) ℚ E := by
  letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  exact ((integralBasis M hfg hspan).baseChange ℚ).map (rationalTensorEquiv M hspan)

@[simp]
theorem integralRationalBasis_coe (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤)
    (i : Fin (Module.finrank ℚ K * Module.finrank K E)) :
    integralRationalBasis M hfg hspan i = (integralBasis M hfg hspan i : E) := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  rw [integralRationalBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    rationalTensorEquiv_tmul, map_one, one_smul]

theorem mem_iff_integerLinearCombination (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (x : E) :
    x ∈ M ↔ ∃ c : Fin (Module.finrank ℚ K * Module.finrank K E) → ℤ,
      ∑ i, c i • (integralBasis M hfg hspan i : E) = x := by
  constructor
  · intro hx
    let y : M := ⟨x, hx⟩
    refine ⟨fun i => (integralBasis M hfg hspan).repr y i, ?_⟩
    simpa only [map_sum, map_smul, LinearMap.restrictScalars_apply,
      Submodule.subtype_apply, y] using
      congrArg (M.subtype.restrictScalars ℤ) ((integralBasis M hfg hspan).sum_repr y)
  · rintro ⟨c, hc⟩
    let y : M := ∑ i, c i • integralBasis M hfg hspan i
    have hy : (y : E) = x := by
      change (M.subtype.restrictScalars ℤ) (∑ i, c i • integralBasis M hfg hspan i) = x
      simpa only [map_sum, map_smul, LinearMap.restrictScalars_apply,
        Submodule.subtype_apply] using hc
    exact hy ▸ y.property

end ArakelovGeometry.NumberFieldFullLattice

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}

/-- An integral basis of the pure global unit-ball lattice, indexed by its rational rank. -/
def normalizedGlobalUnitBallIntegerBasis
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hdom : ξ.IsDominated]
    [hξ : ξ.IsUltrametric] [hpure : ξ.IsPureAtFinitePlaces] :
    Module.Basis (Fin (Module.finrank ℚ K * Module.finrank K E)) ℤ
      (ξ.globalUnitBallModule) :=
  let hm := hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure
  NumberFieldFullLattice.integralBasis (ξ.globalUnitBallModule) hm.1 hm.2.2

theorem IsDominated.pure_normalizedGlobalUnitBall_integerRank (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces) :
    Module.finrank ℤ (ξ.globalUnitBallModule) =
      Module.finrank ℚ K * Module.finrank K E := by
  have hm := hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure
  exact NumberFieldFullLattice.finrank_integer (ξ.globalUnitBallModule) hm.1 hm.2.2

/-- The rational basis induced by an integral basis of the pure global unit-ball lattice. -/
def normalizedGlobalUnitBallRationalBasis
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hdom : ξ.IsDominated]
    [hξ : ξ.IsUltrametric] [hpure : ξ.IsPureAtFinitePlaces] :
    letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
    Module.Basis (Fin (Module.finrank ℚ K * Module.finrank K E)) ℚ E := by
  letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  have hm := hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure
  exact NumberFieldFullLattice.integralRationalBasis (ξ.globalUnitBallModule) hm.1 hm.2.2

@[simp]
theorem normalizedGlobalUnitBallRationalBasis_coe
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [ξ.IsDominated]
    [ξ.IsUltrametric] [ξ.IsPureAtFinitePlaces]
    (i : Fin (Module.finrank ℚ K * Module.finrank K E)) :
    ξ.normalizedGlobalUnitBallRationalBasis i =
      (ξ.normalizedGlobalUnitBallIntegerBasis i : E) := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  exact NumberFieldFullLattice.integralRationalBasis_coe _ _ _ i

end ArakelovGeometry.NormFamily

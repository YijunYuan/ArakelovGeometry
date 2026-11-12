/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.IntegerBasis
public import ArakelovGeometry.NumberTheory.NumberField.TraceDual.Basic
public import Mathlib.RingTheory.DedekindDomain.Different

import Mathlib.Topology.Sheaves.Init

/-!
# Integral trace duality on the original full lattice

The dual submodule consists of original K-linear functionals whose original
values have integral trace on M. Its restriction is the literal integer dual.
The usual codifferent criterion is proved, not assumed as a certificate.
-/

@[expose] public section

noncomputable section

open scoped NumberField TensorProduct nonZeroDivisors

namespace ArakelovGeometry.NumberFieldIntegralTraceDual

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E]

/-- The literal trace-integral submodule of the original K-linear dual. -/
def integralTraceDual (M : Submodule (𝓞 K) E) : Submodule (𝓞 K) (Module.Dual K E) where
  carrier := {f | ∀ m : M, Algebra.trace ℚ K (f (m : E)) ∈
    LinearMap.range (Algebra.linearMap ℤ ℚ)}
  zero_mem' := by intro m; simp
  add_mem' hf hg := by
    intro m
    simpa using (LinearMap.range (Algebra.linearMap ℤ ℚ)).add_mem (hf m) (hg m)
  smul_mem' a f hf := by
    intro m
    have h := hf (a • m)
    have he : f ((a • m : M) : E) = (a • f) (m : E) :=
      f.map_smul_of_tower a (m : E)
    rw [he] at h
    exact h

@[simp]
theorem mem_integralTraceDual (M : Submodule (𝓞 K) E) (f : Module.Dual K E) :
    f ∈ integralTraceDual M ↔ ∀ m : M, Algebra.trace ℚ K (f (m : E)) ∈
      LinearMap.range (Algebra.linearMap ℤ ℚ) := Iff.rfl

/-- Integers identify with the range of their canonical embedding into the rationals. -/
def integerRangeEquiv : ℤ ≃ₗ[ℤ] LinearMap.range (Algebra.linearMap ℤ ℚ) :=
  LinearEquiv.ofInjective (Algebra.linearMap ℤ ℚ) Int.cast_injective

/-- Recovering the integer representative preserves its rational value. -/
@[simp]
theorem integerRangeEquiv_symm_cast (q : LinearMap.range (Algebra.linearMap ℤ ℚ)) :
    (integerRangeEquiv.symm q : ℚ) = (q : ℚ) :=
  congrArg Subtype.val (integerRangeEquiv.apply_symm_apply q)

/-- Original evaluation followed by the unique integral trace value. -/
def traceRestriction (M : Submodule (𝓞 K) E) :
    integralTraceDual M →ₗ[ℤ] Module.Dual ℤ M where
  toFun f :=
    { toFun := fun m => integerRangeEquiv.symm ⟨Algebra.trace ℚ K (f.1 (m : E)), f.2 m⟩
      map_add' m n := by
        apply (Int.cast_injective (α := ℚ))
        simp
      map_smul' a m := by
        apply (Int.cast_injective (α := ℚ))
        simp
        simpa only [zsmul_eq_mul] using
          (Algebra.trace ℚ K).map_smul_of_tower a (f.1 (m : E)) }
  map_add' f g := by
    apply LinearMap.ext
    intro m
    apply (Int.cast_injective (α := ℚ))
    simp
  map_smul' a f := by
    apply LinearMap.ext
    intro m
    apply (Int.cast_injective (α := ℚ))
    simp
    simpa only [zsmul_eq_mul] using
      (Algebra.trace ℚ K).map_smul_of_tower a (f.1 (m : E))

@[simp]
theorem traceRestriction_apply (M : Submodule (𝓞 K) E) (f : integralTraceDual M) (m : M) :
    (traceRestriction M f m : ℚ) = Algebra.trace ℚ K (f.1 (m : E)) :=
  congrArg Subtype.val (integerRangeEquiv.apply_symm_apply _)

theorem mem_integralTraceDual_iff_codifferent (M : Submodule (𝓞 K) E)
    (f : Module.Dual K E) :
    f ∈ integralTraceDual M ↔ ∀ m : M,
      f (m : E) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  constructor
  · intro hf m
    apply (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) (by exact one_ne_zero)).mpr
    intro y hy
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hy
    have he : f ((a • m : M) : E) = f (m : E) * algebraMap (𝓞 K) K a := by
      simpa only [SetLike.val_smul, Algebra.smul_def, mul_comm] using
        f.map_smul_of_tower a (m : E)
    rw [Algebra.traceForm_apply, ← he]
    obtain ⟨z, hz⟩ := hf (a • m)
    exact ⟨z, hz⟩
  · intro hf m
    have h := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ)
      (by exact one_ne_zero)).mp (hf m) 1 (by simp)
    simp only [Algebra.traceForm_apply, mul_one] at h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, hz⟩

/-- Extend an original integer functional through the canonical rational tensor. -/
def rationalExtension (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) (φ : Module.Dual ℤ M) :
    letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
    Module.Dual ℚ E := by
  letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  exact (((Algebra.linearMap ℤ ℚ).comp φ).liftBaseChange ℚ).comp
    (NumberFieldFullLattice.rationalTensorEquiv M hspan).symm.toLinearMap

@[simp]
theorem rationalExtension_apply (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) (φ : Module.Dual ℤ M) (m : M) :
    rationalExtension M hspan φ (m : E) = (φ m : ℚ) := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  let e := NumberFieldFullLattice.rationalTensorEquiv M hspan
  have he : e (1 ⊗ₜ[ℤ] m) = (m : E) := by
    simp [e]
  have hi : e.symm (m : E) = 1 ⊗ₜ[ℤ] m := by
    calc
      e.symm (m : E) = e.symm (e (1 ⊗ₜ[ℤ] m)) := congrArg e.symm he.symm
      _ = 1 ⊗ₜ[ℤ] m := e.symm_apply_apply _
  change ((Algebra.linearMap ℤ ℚ).comp φ).liftBaseChange ℚ (e.symm (m : E)) = _
  rw [hi, LinearMap.liftBaseChange_tmul]
  simp

theorem traceRestriction_injective (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    Function.Injective (traceRestriction M) := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  let : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  intro f g h
  apply Subtype.ext
  apply NumberFieldTraceDual.traceMap_injective (K := K) (E := E)
  apply LinearMap.ext
  intro x
  let e := NumberFieldFullLattice.rationalTensorEquiv M hspan
  obtain ⟨z, rfl⟩ := e.surjective x
  induction z using TensorProduct.inductionOn with
  | tmul q m =>
      rw [NumberFieldFullLattice.rationalTensorEquiv_tmul]
      change NumberFieldTraceDual.traceMap f.1 (q • (m : E)) =
        NumberFieldTraceDual.traceMap g.1 (q • (m : E))
      rw [map_smul, map_smul]
      congr 1
      change Algebra.trace ℚ K (f.1 (m : E)) = Algebra.trace ℚ K (g.1 (m : E))
      rw [← traceRestriction_apply, ← traceRestriction_apply]
      exact congrArg (fun φ : Module.Dual ℤ M => (φ m : ℚ)) h
  | add u v hu hv =>
      simpa only [map_add] using congrArg₂ (· + ·) hu hv

variable [FiniteDimensional K E]

/-- The original K-linear representative of an integer functional on M. -/
def traceExtension (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) (φ : Module.Dual ℤ M) :
    integralTraceDual M := by
  letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  letI : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  refine ⟨(NumberFieldTraceDual.traceEquiv (K := K)).symm (rationalExtension M hspan φ), ?_⟩
  intro m
  rw [NumberFieldTraceDual.traceEquiv_symm_trace, rationalExtension_apply]
  exact ⟨φ m, rfl⟩

@[simp]
theorem traceExtension_apply (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) (φ : Module.Dual ℤ M) (m : M) :
    Algebra.trace ℚ K ((traceExtension M hspan φ).1 (m : E)) = (φ m : ℚ) := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  let : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  exact (NumberFieldTraceDual.traceEquiv_symm_trace (rationalExtension M hspan φ)
    (m : E)).trans (rationalExtension_apply M hspan φ m)

@[simp]
theorem traceRestriction_traceExtension (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) (φ : Module.Dual ℤ M) :
    traceRestriction M (traceExtension M hspan φ) = φ := by
  apply LinearMap.ext
  intro m
  apply (Int.cast_injective (α := ℚ))
  rw [traceRestriction_apply, traceExtension_apply]

theorem traceRestriction_surjective (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    Function.Surjective (traceRestriction M) :=
  fun φ => ⟨traceExtension M hspan φ, traceRestriction_traceExtension M hspan φ⟩

/-- The actual integer dual identification of the original trace-integral lattice. -/
def integralTraceEquiv (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    integralTraceDual M ≃ₗ[ℤ] Module.Dual ℤ M :=
  LinearEquiv.ofBijective (traceRestriction M)
    ⟨traceRestriction_injective M hspan, traceRestriction_surjective M hspan⟩

@[simp]
theorem integralTraceEquiv_apply (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) (f : integralTraceDual M) (m : M) :
    (integralTraceEquiv M hspan f m : ℚ) = Algebra.trace ℚ K (f.1 (m : E)) :=
  traceRestriction_apply M f m

@[simp]
theorem traceExtension_traceRestriction (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) (f : integralTraceDual M) :
    traceExtension M hspan (traceRestriction M f) = f := by
  apply traceRestriction_injective M hspan
  exact traceRestriction_traceExtension M hspan _

end ArakelovGeometry.NumberFieldIntegralTraceDual

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}

/-- The original dominated pure global ball has its actual integer trace dual. -/
def normalizedGlobalUnitBallIntegralTraceEquiv
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) [hdom : ξ.IsDominated]
    [hξ : ξ.IsUltrametric] [hpure : ξ.IsPureAtFinitePlaces] :
    NumberFieldIntegralTraceDual.integralTraceDual (ξ.globalUnitBallModule) ≃ₗ[ℤ]
      Module.Dual ℤ (ξ.globalUnitBallModule) :=
  NumberFieldIntegralTraceDual.integralTraceEquiv (ξ.globalUnitBallModule)
    (hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure).2.2

@[simp]
theorem normalizedGlobalUnitBallIntegralTraceEquiv_apply
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    [ξ.IsDominated] [ξ.IsUltrametric] [ξ.IsPureAtFinitePlaces]
    (f : NumberFieldIntegralTraceDual.integralTraceDual (ξ.globalUnitBallModule))
    (m : ξ.globalUnitBallModule) :
    (ξ.normalizedGlobalUnitBallIntegralTraceEquiv f m : ℚ) =
      Algebra.trace ℚ K (f.1 (m : E)) :=
  NumberFieldIntegralTraceDual.traceRestriction_apply _ _ _

end ArakelovGeometry.NormFamily

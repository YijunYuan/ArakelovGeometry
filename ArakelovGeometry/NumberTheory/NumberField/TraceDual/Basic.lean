/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.NumberTheory.NumberField.Basic

/-!
# The actual rational trace dual of a number-field vector space

Trace composition acts on the original linear functionals and original space.
Nondegeneracy proves injectivity without a dimension hypothesis on the space;
finite dimension gives the rational-linear equivalence used by integral duality.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.NumberFieldTraceDual

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [Module ℚ E] [IsScalarTower ℚ K E]

/-- Trace composition on the original dual space. -/
def traceMap : Module.Dual K E →ₗ[ℚ] Module.Dual ℚ E where
  toFun f := (Algebra.trace ℚ K).comp (f.restrictScalars ℚ)
  map_add' f g := by ext x; simp
  map_smul' a f := by ext x; simp

@[simp]
theorem traceMap_apply (f : Module.Dual K E) (x : E) :
    traceMap f x = Algebra.trace ℚ K (f x) := rfl

theorem traceMap_injective : Function.Injective (traceMap (K := K) (E := E)) := by
  intro f g h
  ext x
  have hz : f x - g x = 0 := (traceForm_nondegenerate ℚ K).1 _ (by
    intro a
    have ha := congrArg (fun ℓ : Module.Dual ℚ E => ℓ (a • x)) h
    simpa [Algebra.traceForm_apply, mul_comm, map_sub] using sub_eq_zero.mpr ha)
  exact sub_eq_zero.mp hz

variable [FiniteDimensional K E]

theorem traceMap_surjective : Function.Surjective (traceMap (K := K) (E := E)) := by
  let : FiniteDimensional ℚ E := Module.Finite.trans K E
  let : FiniteDimensional ℚ (Module.Dual K E) := Module.Finite.trans K _
  have hd : Module.finrank ℚ (Module.Dual K E) = Module.finrank ℚ (Module.Dual ℚ E) := by
    rw [← Module.finrank_mul_finrank ℚ K (Module.Dual K E),
      Subspace.dual_finrank_eq, Module.finrank_mul_finrank, Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp traceMap_injective

/-- The canonical trace composition equivalence of the original rational duals. -/
def traceEquiv : Module.Dual K E ≃ₗ[ℚ] Module.Dual ℚ E :=
  LinearEquiv.ofBijective traceMap ⟨traceMap_injective, traceMap_surjective⟩

@[simp]
theorem traceEquiv_apply (f : Module.Dual K E) (x : E) :
    traceEquiv f x = Algebra.trace ℚ K (f x) := rfl

@[simp]
theorem traceEquiv_symm_trace (ℓ : Module.Dual ℚ E) (x : E) :
    Algebra.trace ℚ K (traceEquiv.symm ℓ x) = ℓ x :=
  congrArg (fun f : Module.Dual ℚ E => f x) (traceEquiv.apply_symm_apply ℓ)

theorem existsUnique_trace_functional (ℓ : Module.Dual ℚ E) :
    ∃! f : Module.Dual K E, ∀ x : E, Algebra.trace ℚ K (f x) = ℓ x := by
  refine ⟨traceEquiv.symm ℓ, fun x => traceEquiv_symm_trace ℓ x, ?_⟩
  intro f hf
  apply traceMap_injective
  ext x
  exact (hf x).trans (traceEquiv_symm_trace ℓ x).symm

end ArakelovGeometry.NumberFieldTraceDual

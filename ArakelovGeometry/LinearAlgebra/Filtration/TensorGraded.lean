/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.Graded
public import ArakelovGeometry.LinearAlgebra.Filtration.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Canonical graded tensor maps

Tensoring the two step inclusions and then taking the quotient gives a map
from each pair of grades into the grade at their total weight. The source of
the assembled map retains every pair with that total weight.
-/

@[expose] public section

open scoped TensorProduct

namespace Submodule

variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]

variable {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}

/-- Tensoring a strict left-factor vector with a filtered right-factor vector raises total weight. -/
theorem tmul_mem_tensorFiltration_rightLimit_left (hF : Antitone F)
    {t u γ : ℝ} (h : t + u = γ) {x : E} {y : V}
    (hx : x ∈ filtrationRightLimit F t) (hy : y ∈ G u) :
    x ⊗ₜ[K] y ∈ filtrationRightLimit (tensorFiltration F G) γ := by
  obtain ⟨ε, hε, hx⟩ := (mem_rightLimit_iff hF t x).mp hx
  exact mem_iSup_of_mem ⟨t + ε + u, by linarith⟩
    (tmul_mem_tensorFiltration (F := F) (G := G) le_rfl hx hy)

/-- Tensoring a filtered left-factor vector with a strict right-factor vector raises total weight. -/
theorem tmul_mem_tensorFiltration_rightLimit_right (hG : Antitone G)
    {t u γ : ℝ} (h : t + u = γ) {x : E} {y : V}
    (hx : x ∈ F t) (hy : y ∈ filtrationRightLimit G u) :
    x ⊗ₜ[K] y ∈ filtrationRightLimit (tensorFiltration F G) γ := by
  obtain ⟨ε, hε, hy⟩ := (mem_rightLimit_iff hG u y).mp hy
  exact mem_iSup_of_mem ⟨t + (u + ε), by linarith⟩
    (tmul_mem_tensorFiltration (F := F) (G := G) le_rfl hx hy)

/-- The tensor of the step inclusions, with codomain the step at the total weight. -/
noncomputable def tensorFiltrationStepMap (F : ℝ → Submodule K E)
    (G : ℝ → Submodule K V) {t u γ : ℝ} (h : t + u = γ) :
    F t ⊗[K] G u →ₗ[K] tensorFiltration F G γ :=
  (TensorProduct.mapIncl (F t) (G u)).codRestrict (tensorFiltration F G γ) (by
    intro x
    exact (show LinearMap.range (TensorProduct.mapIncl (F t) (G u)) ≤
        tensorFiltration F G γ from
      le_iSup_of_le t (le_iSup_of_le u (le_iSup_of_le h.symm.le le_rfl))) ⟨x, rfl⟩)

/-- The canonical map from the tensor product of two steps to the total-weight grade. -/
noncomputable def tensorFiltrationGradedLift (F : ℝ → Submodule K E)
    (G : ℝ → Submodule K V) {t u γ : ℝ} (h : t + u = γ) :
    F t ⊗[K] G u →ₗ[K] FiltrationGraded (tensorFiltration F G) γ :=
  (filtrationGradedMk (tensorFiltration F G) γ).comp (tensorFiltrationStepMap F G h)

/-- The two strict-factor tensor subspaces are killed in the total-weight grade. -/
theorem tensorFiltrationGradedLift_ker (hF : Antitone F) (hG : Antitone G)
    {t u γ : ℝ} (h : t + u = γ) :
    LinearMap.range (TensorProduct.map
        ((filtrationRightLimit F t).comap (F t).subtype).subtype
        (LinearMap.id : G u →ₗ[K] G u)) ⊔
      LinearMap.range (TensorProduct.map (LinearMap.id : F t →ₗ[K] F t)
        ((filtrationRightLimit G u).comap (G u).subtype).subtype) ≤
      LinearMap.ker (tensorFiltrationGradedLift F G h) := by
  apply sup_le
  · rintro _ ⟨x, rfl⟩
    induction x with
    | tmul x y =>
      apply (filtrationGradedMk_eq_zero _ _ _).mpr
      exact tmul_mem_tensorFiltration_rightLimit_left hF h x.property y.property
    | add x y hx hy =>
      simpa only [map_add] using add_mem hx hy
  · rintro _ ⟨x, rfl⟩
    induction x with
    | tmul x y =>
      apply (filtrationGradedMk_eq_zero _ _ _).mpr
      exact tmul_mem_tensorFiltration_rightLimit_right hG h x.property y.property
    | add x y hx hy =>
      simpa only [map_add] using add_mem hx hy

/-- The canonical pair map on actual grades; it need not cover the whole grade by itself. -/
noncomputable def tensorFiltrationGradedPair (hF : Antitone F) (hG : Antitone G)
    {t u γ : ℝ} (h : t + u = γ) :
    FiltrationGraded F t ⊗[K] FiltrationGraded G u →ₗ[K]
      FiltrationGraded (tensorFiltration F G) γ :=
  (Submodule.liftQ _ (tensorFiltrationGradedLift F G h)
      (tensorFiltrationGradedLift_ker hF hG h)).comp
    (TensorProduct.quotientTensorQuotientEquiv
      ((filtrationRightLimit F t).comap (F t).subtype)
      ((filtrationRightLimit G u).comap (G u).subtype)).toLinearMap

@[simp]
theorem tensorFiltrationGradedPair_mk (hF : Antitone F) (hG : Antitone G)
    {t u γ : ℝ} (h : t + u = γ) (x : F t) (y : G u) :
    tensorFiltrationGradedPair hF hG h
        (filtrationGradedMk F t x ⊗ₜ[K] filtrationGradedMk G u y) =
      filtrationGradedMk (tensorFiltration F G) γ
        (tensorFiltrationStepMap F G h (x ⊗ₜ[K] y)) := rfl

/-- Assemble all pairs with the same total weight, retaining every collision. -/
noncomputable def tensorFiltrationGradedSum (hF : Antitone F) (hG : Antitone G) (γ : ℝ) :
    (⨁ p : {p : ℝ × ℝ // p.1 + p.2 = γ},
      FiltrationGraded F p.val.1 ⊗[K] FiltrationGraded G p.val.2) →ₗ[K]
      FiltrationGraded (tensorFiltration F G) γ :=
  DirectSum.toModule K _ _ (fun p ↦ tensorFiltrationGradedPair hF hG p.property)

end Submodule

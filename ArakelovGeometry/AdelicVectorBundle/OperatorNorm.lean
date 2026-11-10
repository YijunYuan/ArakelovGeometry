/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.Comparison

/-!
# Local operator norms between norm families

A rational linear map is extended to the actual completed fibres before its
operator norm is evaluated. The operator seminorm API works also for trivial
absolute values and zero-dimensional source or target spaces.
-/

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

/-- The norm of a rational map after extension to the actual completed fibres. -/
noncomputable def operatorNorm (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (f : E →ₗ[K] F) : ℝ :=
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := η.fibreNormedAddCommGroup ω
  let := η.fibreNormedSpace ω
  linearMapOperatorSeminorm (f.baseChange (S.ϕ ω).Completion)

theorem operatorNorm_nonneg (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (f : E →ₗ[K] F) : 0 ≤ ξ.operatorNorm η ω f := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := η.fibreNormedAddCommGroup ω
  let := η.fibreNormedSpace ω
  exact apply_nonneg linearMapOperatorSeminorm _

/-- The operator norm bounds every vector in the completed source fibre. -/
theorem norm_baseChange_le_operatorNorm (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (f : E →ₗ[K] F) (x : (S.ϕ ω).Completion ⊗[K] E) :
    η.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤
      ξ.operatorNorm η ω f * ξ.norm ω x := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := η.fibreNormedAddCommGroup ω
  let := η.fibreNormedSpace ω
  exact norm_linearMap_apply_le (f.baseChange (S.ϕ ω).Completion) x

/-- A nonnegative uniform evaluation bound bounds the local operator norm. -/
theorem operatorNorm_le (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (f : E →ₗ[K] F) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x, η.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ C * ξ.norm ω x) :
    ξ.operatorNorm η ω f ≤ C := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := η.fibreNormedAddCommGroup ω
  let := η.fibreNormedSpace ω
  exact linearMapOperatorSeminorm_le _ hC hf

/-- The zero map has local operator norm zero, including zero-dimensional fibres. -/
@[simp]
theorem operatorNorm_zero (ξ : NormFamily S E) (η : NormFamily S F) (ω : S.Ω) :
    ξ.operatorNorm η ω 0 = 0 := by
  apply le_antisymm _ (ξ.operatorNorm_nonneg η ω 0)
  apply ξ.operatorNorm_le η ω 0 le_rfl
  simp

/-- The local operator norm is the supremum of the completed evaluation ratios. -/
theorem operatorNorm_eq_sSup (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (f : E →ₗ[K] F) :
    ξ.operatorNorm η ω f = sSup (Set.range fun x ↦
      η.norm ω (f.baseChange (S.ϕ ω).Completion x) / ξ.norm ω x) := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := η.fibreNormedAddCommGroup ω
  let := η.fibreNormedSpace ω
  exact linearMapOperatorSeminorm_eq_sSup _

end ArakelovGeometry.NormFamily

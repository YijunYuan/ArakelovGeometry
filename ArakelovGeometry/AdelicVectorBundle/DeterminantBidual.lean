/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.DeterminantComparison
import ArakelovGeometry.AdelicVectorBundle.DualMap

/-!
# Completed determinant norms and bidualization

The actual bidual is pulled back by canonical evaluation on the original
rational space. Its dual norm equals the original dual norm. At finite places,
injective tensor norms therefore agree, and the proved injective determinant
quotient gives determinant equality. At normalized infinite places, the
original completed norms already agree with their biduals.
-/

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Dualizing the canonically pulled-back bidual recovers the original dual family. -/
theorem dual_dual_pullback_dual_eq (ξ : NormFamily S E) :
    (ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)).dual =
      ξ.dual := by
  ext ω z
  apply le_antisymm
  · have h := ξ.dual.dual.pullback_dual_norm_le
      (Module.Dual.eval K E) (Module.eval_apply_injective K) ω
      ((Module.Dual.eval K (Module.Dual K E)).baseChange (S.ϕ ω).Completion z)
    have he : (Module.Dual.eval K E).dualMap ∘ₗ
        Module.Dual.eval K (Module.Dual K E) = LinearMap.id := by
      ext ℓ x
      rfl
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, he,
      LinearMap.baseChange_id, LinearMap.id_apply, ξ.dual_dual_dual_norm_eval] at h
    exact h
  · exact (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).dual_norm_antitone ξ ω
        (ξ.dual_dual_norm_eval_le ω) z

section Tensor

variable {ι : Type wι} [Fintype ι] {V : ι → Type w}
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  [∀ i, FiniteDimensional K (V i)]

/-- The injective tensor norm depends only on the actual completed dual norms. -/
theorem injectiveTensor_congr_of_dual_eq (ξ η : ∀ i, NormFamily S (V i))
    (h : ∀ i, (ξ i).dual = (η i).dual) : injectiveTensor ξ = injectiveTensor η := by
  ext ω z
  rw [injectiveTensor_norm_eq_sSup ξ, injectiveTensor_norm_eq_sSup η]
  simp only [h]

end Tensor

/-- Canonical bidualization preserves the actual completed determinant family,
without assuming the original finite-place norms ultrametric. -/
theorem determinant_dual_dual_pullback (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ξ.dual.dual.pullback (Module.Dual.eval K E)
      (Module.eval_apply_injective K)).determinant = ξ.determinant := by
  let η := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
  have hε : injectiveTensor (fun _ : Fin (Module.finrank K E) => η) =
      injectiveTensor (fun _ : Fin (Module.finrank K E) => ξ) :=
    injectiveTensor_congr_of_dual_eq _ _ (fun _ => ξ.dual_dual_pullback_dual_eq)
  change η.determinant = ξ.determinant
  ext ω z
  by_cases hω : ω ∈ S.Ωfin
  · rw [η.determinant_eq_exteriorPower, ξ.determinant_eq_exteriorPower]
    simp only [exteriorPower, pushforward_norm_eq_sInf,
      mixedTensor_norm_of_mem_Ωfin _ ω hω, hε]
  · have he : ∀ x, η.norm ω x = ξ.norm ω x :=
      ξ.dual_dual_norm_eval_eq_of_isRCLike ω (hN ω hω)
    exact le_antisymm (η.determinant_norm_mono ξ ω (fun x => (he x).le) z)
      (ξ.determinant_norm_mono η ω (fun x => (he x).symm.le) z)

end ArakelovGeometry.NormFamily

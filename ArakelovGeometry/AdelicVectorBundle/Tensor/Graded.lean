/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.TensorGraded
public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairMap

/-!
# Actual norms and contractions on filtration grades

Every grade carries the restriction followed by the quotient of the original
norm family. The canonical graded map descends a completed contraction by
comparing every completed lift, including at trivially valued places.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {V : Type w'} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The actual grade norm: first restrict the ambient family, then take its
canonical quotient by the strict right limit inside the step. -/
noncomputable def filtrationGraded (ξ : NormFamily S E)
    (F : ℝ → Submodule K E) (t : ℝ) :
    NormFamily S (Submodule.FiltrationGraded F t) :=
  (ξ.restrict (F t)).quotient
    ((Submodule.filtrationRightLimit F t).comap (F t).subtype)

/-- Actual grades of Hermitian norm families are Hermitian, also in rank zero. -/
theorem IsHermitian.filtrationGraded {ξ : NormFamily S E}
    {hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hξ : ξ.IsHermitian hN) (F : ℝ → Submodule K E) (t : ℝ) :
    (ξ.filtrationGraded F t).IsHermitian hN :=
  (hξ.restrict (F t)).quotient _

/-- Every completed lift bounds the actual grade norm. -/
theorem filtrationGraded_norm_mk_le (ξ : NormFamily S E)
    (F : ℝ → Submodule K E) (t : ℝ) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] F t) :
    (ξ.filtrationGraded F t).norm ω
        ((Submodule.filtrationGradedMk F t).baseChange (S.ϕ ω).Completion x) ≤
      (ξ.restrict (F t)).norm ω x :=
  (ξ.restrict (F t)).quotient_norm_mk_le _ ω x

/-- A commuting pair of quotient maps descends a completed contraction. -/
theorem quotientMap_norm_le (ξ : NormFamily S E) (η : NormFamily S V)
    (f : E →ₗ[K] V) (U : Submodule K E) (T : Submodule K V)
    (g : (E ⧸ U) →ₗ[K] (V ⧸ T)) (hc : g.comp U.mkQ = T.mkQ.comp f)
    (ω : S.Ω)
    (hf : ∀ x, η.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⧸ U)) :
    (η.quotient T).norm ω (g.baseChange (S.ϕ ω).Completion z) ≤
      (ξ.quotient U).norm ω z := by
  apply (ξ.le_quotientSeminorm_iff U.mkQ U.mkQ_surjective ω z _).mpr
  intro x hx
  have he := DFunLike.congr_fun
    (congrArg (fun p ↦ p.baseChange (S.ϕ ω).Completion) hc) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at he
  rw [← hx, he]
  exact (η.quotient_norm_mk_le T ω _).trans (hf x)

/-- A threshold-preserving contraction induces A5's canonical graded map as a
contraction on every completed vector for the actual subquotient norms. -/
theorem filtrationGradedMap_norm_le (ξ : NormFamily S E) (η : NormFamily S V)
    {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
    (f : E →ₗ[K] V) (hf : ∀ t, F t ≤ (G t).comap f) (t : ℝ) (ω : S.Ω)
    (hn : ∀ x, η.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] Submodule.FiltrationGraded F t) :
    (η.filtrationGraded G t).norm ω
        ((Submodule.filtrationGradedMap f hf t).baseChange (S.ϕ ω).Completion z) ≤
      (ξ.filtrationGraded F t).norm ω z := by
  apply quotientMap_norm_le (ξ.restrict (F t)) (η.restrict (G t))
    (Submodule.filtrationStepMap f hf t) _ _ _ (by ext x; rfl) ω
  intro x
  have hc : (G t).subtype.comp (Submodule.filtrationStepMap f hf t) =
      f.comp (F t).subtype := by ext y; rfl
  have he := DFunLike.congr_fun
    (congrArg (fun p ↦ p.baseChange (S.ϕ ω).Completion) hc) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at he
  simp only [restrict_norm]
  rw [he]
  exact hn _

/-- In particular, the canonical graded map to an actual quotient contracts;
its target uses the quotient bundle's original subquotient norm. -/
theorem filtrationGradedMap_pushforward_norm_le (ξ : NormFamily S E)
    (q : E →ₗ[K] V) (hq : Function.Surjective q)
    (F : ℝ → Submodule K E) (t : ℝ) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Submodule.FiltrationGraded F t) :
    ((ξ.pushforward q hq).filtrationGraded (fun s ↦ (F s).map q) t).norm ω
        ((Submodule.filtrationGradedMap q
          (fun s ↦ Submodule.le_comap_map q (F s)) t).baseChange (S.ϕ ω).Completion z) ≤
      (ξ.filtrationGraded F t).norm ω z :=
  filtrationGradedMap_norm_le ξ (ξ.pushforward q hq) q _ t ω
    (ξ.pushforward_norm_le q hq ω) z

end ArakelovGeometry.NormFamily

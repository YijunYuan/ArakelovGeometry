/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DeterminantDuality

/-!
# Local determinant pairing bounds

At finite places the completed determinant pairing bound holds for arbitrary
norm families. At normalized infinite places it needs only an inner product
inducing the norm on that completed fibre. Nearly optimal single-wedge
presentations extend pure-wedge estimates to the actual determinant norms.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)

/-- Any pure-wedge product bound extends to the actual determinant quotient
norms by arbitrarily close single-wedge presentations. Rank zero uses its
accepted exact scalar-line formula. -/
theorem norm_completedDeterminantPairing_le_of_ιMulti_bound (ω : S.Ω)
    (hp : ∀ (f : Fin (Module.finrank K (Module.Dual K E)) →
        (S.ϕ ω).Completion ⊗[K] Module.Dual K E)
      (x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E),
      ‖completedDeterminantPairing K (S.ϕ ω).Completion E
          ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K E) _).symm
            (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ f))
          ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
            (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ x))‖ ≤
        (∏ i, ξ.norm ω (x i)) * ∏ i, ξ.dual.norm ω (f i))
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ ≤
      ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z := by
  by_cases hr : Module.finrank K E = 0
  · exact (ξ.norm_completedDeterminantPairing_of_finrank_eq_zero hr ω z w).le
  have hrpos := Nat.pos_of_ne_zero hr
  have hε (ε : ℝ) (hε : 0 < ε) :
      ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ ≤
        (ξ.determinant.norm ω w + ε) * (ξ.dual.determinant.norm ω z + ε) := by
    obtain ⟨x, hx, hxn⟩ := ξ.exists_determinant_ιMulti_norm_lt hrpos ω w hε
    obtain ⟨f, hf, hfn⟩ := ξ.dual.exists_determinant_ιMulti_norm_lt
      (show 0 < Module.finrank K (Module.Dual K E) by rwa [Subspace.dual_finrank_eq])
      ω z hε
    have h := hp f x
    rw [hf, hx] at h
    exact h.trans (mul_le_mul hxn.le hfn.le
      (Finset.prod_nonneg fun i _ ↦ ξ.dual.norm_nonneg ω (f i))
      (add_nonneg (ξ.determinant.norm_nonneg ω w) hε.le))
  have hlim : Filter.Tendsto (fun ε : ℝ ↦
      (ξ.determinant.norm ω w + ε) * (ξ.dual.determinant.norm ω z + ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z)) := by
    have hc : ContinuousAt (fun ε : ℝ ↦
        (ξ.determinant.norm ω w + ε) * (ξ.dual.determinant.norm ω z + ε)) 0 :=
      (continuousAt_const.add continuousAt_id).mul (continuousAt_const.add continuousAt_id)
    simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hpos
  exact hε ε hpos

/-- The pure-wedge pairing bound at a finite place requires no ultrametric
assumption on the vector-space norm. The completed scalar norm is ultrametric. -/
theorem norm_completedDeterminantPairing_ιMulti_le_finite (ω : S.Ω)
    (hω : ω ∈ S.Ωfin)
    (f : Fin (Module.finrank K (Module.Dual K E)) →
      (S.ϕ ω).Completion ⊗[K] Module.Dual K E)
    (x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K E) _).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ f))
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ x))‖ ≤
      (∏ i, ξ.norm ω (x i)) * ∏ i, ξ.dual.norm ω (f i) := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let g (i : Fin (Module.finrank K E)) := dualBaseChangeEquiv K (S.ϕ ω).Completion E
    (f ((finCongr Subspace.dual_finrank_eq).symm i))
  have hg : (∏ i, linearMapOperatorSeminorm (g i)) = ∏ i, ξ.dual.norm ω (f i) := by
    change (∏ i, ξ.dual.norm ω (f ((finCongr Subspace.dual_finrank_eq).symm i))) = _
    exact Equiv.prod_comp (finCongr (Subspace.dual_finrank_eq (K := K) (V := E))).symm
      (fun i ↦ ξ.dual.norm ω (f i))
  have hL (a b : (S.ϕ ω).Completion) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
    refine UniformSpace.Completion.induction_on₂ a b ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro c d
      simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe]
        using (show ‖c + d‖ ≤ max ‖c‖ ‖d‖ from hω c.ofAbs d.ofAbs)
  let : IsUltrametricDist (S.ϕ ω).Completion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hL
  rw [completedDeterminantPairing_ιMulti]
  change ‖(Matrix.of fun i j ↦ g j (x i)).det‖ ≤ _
  have h := norm_det_pairing_le_of_ultrametric g x
  rw [hg] at h
  exact h

/-- The actual completed determinant pairing is contractive at every finite
place for any norm family, including rank zero. -/
theorem norm_completedDeterminantPairing_le_finite (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ ≤
      ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z :=
  ξ.norm_completedDeterminantPairing_le_of_ιMulti_bound ω
    (ξ.norm_completedDeterminantPairing_ιMulti_le_finite ω hω) z w

/-- A local positive definite inner-product core inducing the prescribed
completed norm proves the pure-wedge pairing estimate. -/
theorem norm_completedDeterminantPairing_ιMulti_le_of_innerProductCore
    (ω : S.Ω) [IsRCLikeNormedField (S.ϕ ω).Completion] :
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    ∀ (c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E)),
      (∀ x, (ξ.norm ω x) ^ 2 = RCLike.re (c.inner x x)) →
      ∀ (f : Fin (Module.finrank K (Module.Dual K E)) →
        (S.ϕ ω).Completion ⊗[K] Module.Dual K E)
      (x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E),
      ‖completedDeterminantPairing K (S.ϕ ω).Completion E
          ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K E) _).symm
            (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ f))
          ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
            (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ x))‖ ≤
        (∏ i, ξ.norm ω (x i)) * ∏ i, ξ.dual.norm ω (f i) := by
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  intro c hc f x
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := innerProductSpaceOfCoreNorm c hc
  let g (i : Fin (Module.finrank K E)) := dualBaseChangeEquiv K (S.ϕ ω).Completion E
    (f ((finCongr Subspace.dual_finrank_eq).symm i))
  have hg : (∏ i, linearMapOperatorSeminorm (g i)) = ∏ i, ξ.dual.norm ω (f i) := by
    change (∏ i, ξ.dual.norm ω (f ((finCongr Subspace.dual_finrank_eq).symm i))) = _
    exact Equiv.prod_comp (finCongr (Subspace.dual_finrank_eq (K := K) (V := E))).symm
      (fun i ↦ ξ.dual.norm ω (f i))
  rw [completedDeterminantPairing_ιMulti]
  change ‖(Matrix.of fun i j ↦ g j (x i)).det‖ ≤ _
  have h := norm_det_pairing_le_of_innerProduct g x Module.finrank_baseChange
  rw [hg] at h
  exact h

/-- The local inner-product hypothesis alone gives the pairing bound for all
actual determinant vectors. No global Hermitian condition is required. -/
theorem norm_completedDeterminantPairing_le_of_innerProductCore
    (ω : S.Ω) [IsRCLikeNormedField (S.ϕ ω).Completion] :
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    ∀ (c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E)),
      (∀ x, (ξ.norm ω x) ^ 2 = RCLike.re (c.inner x x)) →
      ∀ (z : (S.ϕ ω).Completion ⊗[K]
        (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
      (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)),
      ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ ≤
        ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z := by
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  intro c hc z w
  exact ξ.norm_completedDeterminantPairing_le_of_ιMulti_bound ω
    (ξ.norm_completedDeterminantPairing_ιMulti_le_of_innerProductCore ω c hc) z w

/-- Local determinant-dual isometry at every finite place, for any norm family. -/
theorem norm_completedDeterminantPairing_eq_finite (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ =
      ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z :=
  le_antisymm (ξ.norm_completedDeterminantPairing_le_finite ω hω z w)
    (ξ.determinant_norm_mul_dual_le_norm_pairing ω z w)

/-- Local determinant-dual isometry whenever an actual inner-product core
induces the norm at the chosen normalized completion. -/
theorem norm_completedDeterminantPairing_eq_of_innerProductCore
    (ω : S.Ω) [IsRCLikeNormedField (S.ϕ ω).Completion] :
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    ∀ (c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E)),
      (∀ x, (ξ.norm ω x) ^ 2 = RCLike.re (c.inner x x)) →
      ∀ (z : (S.ϕ ω).Completion ⊗[K]
        (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
      (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)),
      ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ =
        ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z := by
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  intro c hc z w
  exact le_antisymm (ξ.norm_completedDeterminantPairing_le_of_innerProductCore ω c hc z w)
    (ξ.determinant_norm_mul_dual_le_norm_pairing ω z w)

end

end ArakelovGeometry.NormFamily

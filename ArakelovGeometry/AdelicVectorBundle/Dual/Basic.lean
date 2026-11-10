/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Subquotient.Restriction.Basic
public import ArakelovGeometry.Analysis.NormedSpace.LinearMapBound
public import ArakelovGeometry.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Dual norm families

The dual norm is the operator norm on the actual completed scalar extension
of the algebraic dual, transported through its canonical base-change equivalence.
This construction includes trivially valued places and the zero-dimensional case.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

variable (ξ : NormFamily S E)

/-- The operator seminorm on the completed algebraic dual, transported along
the canonical scalar-extension equivalence. -/
noncomputable def dualSeminorm (ω : S.Ω) :
    Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] Module.Dual K E) := by
  letI := ξ.fibreNormedAddCommGroup ω
  letI := ξ.fibreNormedSpace ω
  exact linearMapOperatorSeminorm.comp
    (dualBaseChangeEquiv K (S.ϕ ω).Completion E).toLinearMap

/-- The dual seminorm separates zero, since every functional is bounded and
the canonical completed-dual identification is injective. -/
theorem dualSeminorm_eq_zero_iff (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    ξ.dualSeminorm ω z = 0 ↔ z = 0 := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  change linearMapOperatorSeminorm (dualBaseChangeEquiv K (S.ϕ ω).Completion E z) = 0 ↔ _
  rw [linearMapOperatorSeminorm_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

/-- The dual family from Chen–Moriwaki §4.1.1.4, on the actual completed
fibres of `Module.Dual K E`. -/
noncomputable def dual : NormFamily S (Module.Dual K E) where
  norm := ξ.dualSeminorm
  norm_eq_zero_iff := ξ.dualSeminorm_eq_zero_iff

/-- The dual norm is the supremum of evaluation ratios. Including the zero
vector in the range gives value zero when the original space has dimension zero. -/
theorem dual_norm_eq_sSup (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    ξ.dual.norm ω z = sSup (Set.range fun x : (S.ϕ ω).Completion ⊗[K] E ↦
      ‖dualBaseChangeEquiv K (S.ϕ ω).Completion E z x‖ / ξ.norm ω x) := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  exact linearMapOperatorSeminorm_eq_sSup _

/-- Evaluation of a completed functional is bounded by the dual and original norms. -/
theorem norm_dual_apply_le (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    ‖dualBaseChangeEquiv K (S.ϕ ω).Completion E z x‖ ≤
      ξ.dual.norm ω z * ξ.norm ω x := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  exact norm_linearMap_apply_le _ _

/-- A common bound for evaluations is an upper bound for the dual norm. -/
theorem dual_norm_le (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖dualBaseChangeEquiv K (S.ϕ ω).Completion E z x‖ ≤ C * ξ.norm ω x) :
    ξ.dual.norm ω z ≤ C := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  exact linearMapOperatorSeminorm_le _ hC h

/-- Every dual family is ultrametric at the non-Archimedean places, without
requiring the original norm family to be ultrametric. -/
theorem dual_isUltrametric : ξ.dual.IsUltrametric := by
  intro ω hω z t
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  have hL (a b : (S.ϕ ω).Completion) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
    refine UniformSpace.Completion.induction_on₂ a b ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro x y
      simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe]
        using (show ‖x + y‖ ≤ max ‖x‖ ‖y‖ from hω x.ofAbs y.ofAbs)
  change linearMapOperatorSeminorm (dualBaseChangeEquiv K (S.ϕ ω).Completion E (z + t)) ≤
    max (linearMapOperatorSeminorm (dualBaseChangeEquiv K (S.ϕ ω).Completion E z))
      (linearMapOperatorSeminorm (dualBaseChangeEquiv K (S.ϕ ω).Completion E t))
  rw [map_add]
  exact linearMapOperatorSeminorm_add_le_max hL _ _

/-- Evaluation on pure tensors recovers the original algebraic pairing. -/
theorem norm_dual_tmul_apply_tmul_le (ω : S.Ω) (a b : (S.ϕ ω).Completion)
    (ℓ : Module.Dual K E) (x : E) :
    ‖a * b * algebraMap K (S.ϕ ω).Completion (ℓ x)‖ ≤
      ξ.dual.norm ω (a ⊗ₜ[K] ℓ) * ξ.norm ω (b ⊗ₜ[K] x) := by
  simpa only [dualBaseChangeEquiv_tmul_apply_tmul] using
    ξ.norm_dual_apply_le ω (a ⊗ₜ[K] ℓ) (b ⊗ₜ[K] x)

/-- The dual norm vanishes identically in dimension zero. -/
theorem dual_norm_eq_zero_of_subsingleton [Subsingleton E] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) : ξ.dual.norm ω z = 0 :=
  ξ.dual.norm_eq_zero_of_subsingleton ω z

/-- Rescaling the original norm rescales its dual by the reciprocal factor. -/
theorem scale_dual_norm (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    (ξ.scale f hf).dual.norm ω z = (f ω)⁻¹ * ξ.dual.norm ω z := by
  apply le_antisymm
  · apply (ξ.scale f hf).dual_norm_le ω z
      (mul_nonneg (inv_nonneg.mpr (hf ω).le) (ξ.dual.norm_nonneg ω z))
    intro x
    simpa [scale_norm, mul_assoc, mul_left_comm, mul_comm, (hf ω).ne']
      using ξ.norm_dual_apply_le ω z x
  · apply (inv_mul_le_iff₀ (hf ω)).mpr
    apply ξ.dual_norm_le ω z
      (mul_nonneg (hf ω).le ((ξ.scale f hf).dual.norm_nonneg ω z))
    intro x
    simpa only [scale_norm, mul_assoc, mul_left_comm]
      using (ξ.scale f hf).norm_dual_apply_le ω z x

/-- Duality intertwines multiplication by a positive numerical function and
multiplication by its reciprocal. -/
theorem scale_dual (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) :
    (ξ.scale f hf).dual = ξ.dual.scale (fun ω ↦ (f ω)⁻¹)
      (fun ω ↦ inv_pos.mpr (hf ω)) := by
  ext ω z
  exact ξ.scale_dual_norm f hf ω z

/-- Increasing a fibre norm decreases the corresponding dual norm. -/
theorem dual_norm_antitone (η : NormFamily S E) (ω : S.Ω)
    (h : ∀ x, ξ.norm ω x ≤ η.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    η.dual.norm ω z ≤ ξ.dual.norm ω z := by
  apply η.dual_norm_le ω z (ξ.dual.norm_nonneg ω z)
  intro x
  exact (ξ.norm_dual_apply_le ω z x).trans
    (mul_le_mul_of_nonneg_left (h x) (ξ.dual.norm_nonneg ω z))

/-- The canonical evaluation into the completed bidual is a contraction.
This bound requires neither ultrametricity nor an Archimedean normalization. -/
theorem dual_dual_norm_eval_le (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.dual.dual.norm ω ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion x) ≤
      ξ.norm ω x := by
  apply ξ.dual.dual_norm_le ω _ (ξ.norm_nonneg ω x)
  intro z
  rw [dualBaseChangeEquiv_eval, LinearEquiv.dualMap_apply, Module.Dual.eval_apply]
  simpa only [mul_comm] using ξ.norm_dual_apply_le ω z x

/-- The zero-dimensional case of duality, expressed by the source's dimension. -/
theorem dual_norm_eq_zero_of_finrank_eq_zero (h : Module.finrank K E = 0) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) : ξ.dual.norm ω z = 0 := by
  let : Subsingleton E := (Module.finrank_eq_zero_iff_of_free K E).mp h
  exact ξ.dual_norm_eq_zero_of_subsingleton ω z

/-- On a one-dimensional completed fibre, a single nonzero basis vector
computes the operator norm exactly. -/
theorem dual_norm_eq_div_of_basis (ω : S.Ω)
    (b : Module.Basis (Fin 1) (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E))
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    ξ.dual.norm ω z =
      ‖dualBaseChangeEquiv K (S.ϕ ω).Completion E z (b 0)‖ / ξ.norm ω (b 0) := by
  have hn := ξ.norm_pos ω (b.ne_zero 0)
  apply le_antisymm
  · apply ξ.dual_norm_le ω z (div_nonneg (_root_.norm_nonneg _) hn.le)
    intro x
    have hx : (b.repr x) 0 • b 0 = x := by simpa using b.sum_repr x
    conv_lhs => rw [← hx, map_smul, _root_.norm_smul]
    conv_rhs => rw [← hx, ξ.norm_smul]
    apply le_of_eq
    field_simp [hn.ne']
  · exact (div_le_iff₀ hn).mpr (ξ.norm_dual_apply_le ω z (b 0))

/-- The canonical completed evaluation is an isometry for every norm family
on a one-dimensional vector space, including trivially valued places. -/
theorem dual_dual_norm_eval_eq_of_finrank_eq_one (h : Module.finrank K E = 1)
    (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.dual.dual.norm ω ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion x) =
      ξ.norm ω x := by
  let b := (Module.finBasisOfFinrankEq K E h).baseChange (S.ϕ ω).Completion
  let z := (dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (b.coord 0)
  have hz : dualBaseChangeEquiv K (S.ϕ ω).Completion E z = b.coord 0 :=
    (dualBaseChangeEquiv K (S.ϕ ω).Completion E).apply_symm_apply _
  have hn := ξ.norm_pos ω (b.ne_zero 0)
  have hznorm : ξ.dual.norm ω z = (ξ.norm ω (b 0))⁻¹ := by
    rw [ξ.dual_norm_eq_div_of_basis ω b z, hz]
    simp
  apply le_antisymm (ξ.dual_dual_norm_eval_le ω x)
  have hb := ξ.dual.norm_dual_apply_le ω
    ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion x) z
  rw [dualBaseChangeEquiv_eval, LinearEquiv.dualMap_apply, Module.Dual.eval_apply,
    hz, hznorm] at hb
  have hx : (b.repr x) 0 • b 0 = x := by simpa using b.sum_repr x
  calc
    ξ.norm ω x = ‖(b.repr x) 0‖ * ξ.norm ω (b 0) := by
      conv_lhs => rw [← hx, ξ.norm_smul]
    _ ≤ _ := by
      simpa [Module.Basis.coord_apply, mul_assoc, hn.ne'] using
        mul_le_mul_of_nonneg_right hb hn.le

/-- Biduality is isometric in dimensions zero and one without a local
ultrametricity or Archimedean normalization assumption. -/
theorem dual_dual_norm_eval_eq_of_finrank_le_one (h : Module.finrank K E ≤ 1)
    (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.dual.dual.norm ω ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion x) =
      ξ.norm ω x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
  · let : Subsingleton E := (Module.finrank_eq_zero_iff_of_free K E).mp h
    rw [Subsingleton.elim x 0, map_zero, ξ.dual.dual.norm_zero, ξ.norm_zero]
  · exact ξ.dual_dual_norm_eval_eq_of_finrank_eq_one h ω x

/-- Taking the dual of the bidual gives back the dual norm under canonical
evaluation, for every norm family. -/
theorem dual_dual_dual_norm_eval (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    ξ.dual.dual.dual.norm ω
        ((Module.Dual.eval K (Module.Dual K E)).baseChange (S.ϕ ω).Completion z) =
      ξ.dual.norm ω z := by
  apply le_antisymm (ξ.dual.dual_dual_norm_eval_le ω z)
  apply ξ.dual_norm_le ω z (ξ.dual.dual.dual.norm_nonneg ω _)
  intro x
  have hb := ξ.dual.dual.norm_dual_apply_le ω
    ((Module.Dual.eval K (Module.Dual K E)).baseChange (S.ϕ ω).Completion z)
    ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion x)
  simp only [dualBaseChangeEquiv_eval, LinearEquiv.dualMap_apply,
    Module.Dual.eval_apply] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (ξ.dual_dual_norm_eval_le ω x)
    (ξ.dual.dual.dual.norm_nonneg ω _))

/-- Under the canonical identification with the bidual, norm families in
dimensions zero and one equal their bidual families. -/
theorem dual_dual_pullback_eq_of_finrank_le_one (h : Module.finrank K E ≤ 1) :
    ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K) = ξ := by
  ext ω x
  exact ξ.dual_dual_norm_eval_eq_of_finrank_le_one h ω x

/-- Under canonical evaluation, the triple dual family equals the dual family. -/
theorem dual_dual_dual_pullback :
    ξ.dual.dual.dual.pullback (Module.Dual.eval K (Module.Dual K E))
      (Module.eval_apply_injective K) = ξ.dual := by
  ext ω z
  exact ξ.dual_dual_dual_norm_eval ω z

end ArakelovGeometry.NormFamily

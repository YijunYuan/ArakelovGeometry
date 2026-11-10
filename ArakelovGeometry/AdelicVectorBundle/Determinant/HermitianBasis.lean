/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.Tensor.HermitianInnerProduct
import ArakelovGeometry.AdelicVectorBundle.Determinant.DualNorm
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Hermitian determinant volumes of completed bases

The actual determinant pairing and the two Hadamard bounds determine the
volume of a completed basis whose vectors and coordinate duals have norm at
most one. Orthonormal bases satisfy these bounds at infinite places. Empty
bases use the same pairing and product formulas.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)
  {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}

/-- A completed basis and its coordinate duals, both bounded by one, have
actual determinant volume one for a Hermitian family. The empty basis is included. -/
theorem IsHermitian.determinant_norm_completedBasis_eq_one (hξ : ξ.IsHermitian hS)
    (ω : S.Ω)
    (b : Module.Basis (Fin (Module.finrank K E)) (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E))
    (hb : ∀ i, ξ.norm ω (b i) ≤ 1)
    (hf : ∀ i, ξ.dual.norm ω
      ((dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (b.coord i)) ≤ 1) :
    ξ.determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
        (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ b)) = 1 := by
  classical
  let e := finCongr (Subspace.dual_finrank_eq (K := K) (V := E))
  let f (i : Fin (Module.finrank K (Module.Dual K E))) :=
    (dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (b.coord (e i))
  let w := (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
    (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ b)
  let z := (exteriorBaseChangeEquiv K (S.ϕ ω).Completion (Module.Dual K E) _).symm
    (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ f)
  have hp : completedDeterminantPairing K (S.ϕ ω).Completion E z w = 1 := by
    rw [completedDeterminantPairing_ιMulti]
    have hm : (Matrix.of fun i j ↦ b.coord j (b i)) =
        (1 : Matrix (Fin (Module.finrank K E)) (Fin (Module.finrank K E))
          (S.ϕ ω).Completion) := by
      ext i j
      simp [Module.Basis.coord_apply, Matrix.one_apply, Finsupp.single_apply]
    simp only [f, e, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      hm, Matrix.det_one]
  have hw : ξ.determinant.norm ω w ≤ 1 := by
    refine (ξ.determinant_norm_ιMulti_le ω b).trans ?_
    calc
      _ ≤ ∏ _ : Fin (Module.finrank K E), (1 : ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => ξ.norm_nonneg ω (b i)) (fun i _ => hb i)
      _ = 1 := by simp
  have hz : ξ.dual.determinant.norm ω z ≤ 1 := by
    refine (ξ.dual.determinant_norm_ιMulti_le ω f).trans ?_
    calc
      _ ≤ ∏ _ : Fin (Module.finrank K (Module.Dual K E)), (1 : ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => ξ.dual.norm_nonneg ω (f i))
          (fun i _ => hf (e i))
      _ = 1 := by simp
  have h := hξ.norm_completedDeterminantPairing_le ξ ω z w
  rw [hp, norm_one] at h
  exact le_antisymm hw (h.trans
    (mul_le_of_le_one_right (ξ.determinant.norm_nonneg ω w) hz))

/-- An orthonormal basis of the actual completed fibre has determinant
volume one at an infinite place. Its coordinate-dual bounds are produced
from Cauchy–Schwarz; no determinant equality is assumed. -/
theorem IsHermitian.determinant_norm_orthonormalBasis (hξ : ξ.IsHermitian hS)
    (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hS ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := ξ.fibreNormedAddCommGroup ω
    letI := ξ.fibreNormedSpace ω
    letI := hξ.fibreInnerProductSpace ω hω
    ∀ b : OrthonormalBasis (Fin (Module.finrank K E)) (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E),
      ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ b)) = 1 := by
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := hξ.fibreInnerProductSpace ω hω
  intro b
  apply hξ.determinant_norm_completedBasis_eq_one ξ ω b.toBasis
  · intro i
    change ‖b i‖ ≤ 1
    exact (b.norm_eq_one i).le
  · intro i
    apply ξ.dual_norm_le ω _ zero_le_one
    intro x
    rw [LinearEquiv.apply_symm_apply]
    change ‖b.toBasis.repr x i‖ ≤ 1 * ‖x‖
    rw [OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply]
    simpa only [b.norm_eq_one i, one_mul] using (norm_inner_le_norm (b i) x)

/-- The normalized completed determinant generator is produced by an actual
orthonormal basis. This also produces the empty basis in rank zero. -/
theorem IsHermitian.exists_completedOrthonormalBasis_determinant_norm_eq_one
    (hξ : ξ.IsHermitian hS) (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hS ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := ξ.fibreNormedAddCommGroup ω
    letI := ξ.fibreNormedSpace ω
    letI := hξ.fibreInnerProductSpace ω hω
    ∃ b : OrthonormalBasis (Fin (Module.finrank K E)) (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E),
      ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ b)) = 1 := by
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := hξ.fibreInnerProductSpace ω hω
  let b := (stdOrthonormalBasis (S.ϕ ω).Completion
    ((S.ϕ ω).Completion ⊗[K] E)).reindex (finCongr Module.finrank_baseChange)
  exact ⟨b, hξ.determinant_norm_orthonormalBasis ξ ω hω b⟩

end

end ArakelovGeometry.NormFamily

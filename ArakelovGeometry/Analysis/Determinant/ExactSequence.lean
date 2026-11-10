/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Determinant coordinates in a subspace and quotient

The block determinant formula gives independence of the quotient-vector
lifts in an adapted basis. These are algebraic producers for the canonical
exact-sequence determinant map, before any norm comparison.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {n : ℕ}

/-- The basis determinant induces a scalar coordinate on its actual
top exterior power, including the empty wedge. -/
def determinantCoordinateEquiv (b : Module.Basis (Fin n) K E) :
    (⋀[K]^n E) ≃ₗ[K] K :=
  LinearEquiv.ofBijective (exteriorPower.alternatingMapLinearEquiv b.det) (by
    have hdim : Module.finrank K (⋀[K]^n E) = Module.finrank K K := by
      rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b,
        Fintype.card_fin, Nat.choose_self, Module.finrank_self]
    have hs : Function.Surjective (exteriorPower.alternatingMapLinearEquiv b.det) := by
      intro a
      refine ⟨a • exteriorPower.ιMulti K n b, ?_⟩
      rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
        b.det_self, smul_eq_mul, mul_one]
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hs, hs⟩)

@[simp]
theorem determinantCoordinateEquiv_ιMulti (b : Module.Basis (Fin n) K E)
    (x : Fin n → E) :
    determinantCoordinateEquiv b (exteriorPower.ιMulti K n x) = b.det x :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det x

/-- The inverse coordinate sends a scalar to its multiple of the basis wedge. -/
theorem determinantCoordinateEquiv_symm (b : Module.Basis (Fin n) K E) (a : K) :
    (determinantCoordinateEquiv b).symm a = a • exteriorPower.ιMulti K n b := by
  apply (determinantCoordinateEquiv b).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, determinantCoordinateEquiv_ιMulti,
    b.det_self, smul_eq_mul, mul_one]

omit [FiniteDimensional K E] in
/-- An adapted determinant is the product of the subspace determinant and
the quotient determinant, for every choice of quotient-vector lifts. -/
theorem sumQuot_det (W : Submodule K E)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (bW : Module.Basis ι K W) (bQ : Module.Basis κ K (E ⧸ W))
    (w : ι → W) (v : κ → E) :
    (bW.sumQuot bQ).det (Sum.elim (fun i ↦ (w i : E)) v) =
      bW.det w * bQ.det (fun j ↦ W.mkQ (v j)) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply]
  have hz (i : ι) : W.mkQ (w i) = 0 :=
    (Submodule.Quotient.mk_eq_zero W).mpr (w i).property
  have hm : (bW.sumQuot bQ).toMatrix (Sum.elim (fun i ↦ (w i : E)) v) =
      Matrix.fromBlocks (bW.toMatrix w)
        (Matrix.of fun i j ↦ (bW.sumQuot bQ).repr (v j) (Sum.inl i)) 0
        (bQ.toMatrix (fun j ↦ W.mkQ (v j))) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.fromBlocks, Module.Basis.toMatrix_apply,
        hz, -Submodule.mkQ_apply]
  rw [hm, Matrix.det_fromBlocks_zero₂₁]

omit [FiniteDimensional K E] in
/-- Altering the quotient-vector lifts preserves the adapted determinant. -/
theorem sumQuot_det_eq_of_mkQ_eq (W : Submodule K E)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (bW : Module.Basis ι K W) (bQ : Module.Basis κ K (E ⧸ W))
    (w : ι → W) (v v' : κ → E) (hv : ∀ j, W.mkQ (v j) = W.mkQ (v' j)) :
    (bW.sumQuot bQ).det (Sum.elim (fun i ↦ (w i : E)) v) =
      (bW.sumQuot bQ).det (Sum.elim (fun i ↦ (w i : E)) v') := by
  rw [sumQuot_det, sumQuot_det]
  congr 2
  exact funext hv

end

noncomputable section Sequence

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] (W : Submodule K E) {a b : ℕ}
  (bW : Module.Basis (Fin a) K W) (bQ : Module.Basis (Fin b) K (E ⧸ W))

/-- The determinant-line map in adapted coordinates. Its wedge formula below
shows that it does not depend on either basis or on the quotient lifts. -/
def determinantSequenceEquivOfBases :
    ((⋀[K]^a W) ⊗[K] (⋀[K]^b (E ⧸ W))) ≃ₗ[K] (⋀[K]^(a + b) E) :=
  ((TensorProduct.congr (determinantCoordinateEquiv bW)
    (determinantCoordinateEquiv bQ)).trans (TensorProduct.lid K K)).trans
      (determinantCoordinateEquiv ((bW.sumQuot bQ).reindex finSumFinEquiv)).symm

omit [FiniteDimensional K E] in
/-- The block determinant formula after ordering the two finite factors. -/
theorem sumQuot_fin_det (w : Fin a → W) (v : Fin b → E) :
    ((bW.sumQuot bQ).reindex finSumFinEquiv).det
        (Fin.append (fun i ↦ (w i : E)) v) =
      bW.det w * bQ.det (fun j ↦ W.mkQ (v j)) := by
  rw [Module.Basis.det_reindex]
  convert sumQuot_det W bW bQ w v using 2
  funext i
  cases i <;> simp

/-- The actual map sends two wedge vectors to the wedge of the subspace
vectors followed by any lifts of the quotient vectors. -/
theorem determinantSequenceEquivOfBases_ιMulti (w : Fin a → W) (v : Fin b → E) :
    determinantSequenceEquivOfBases W bW bQ
      (exteriorPower.ιMulti K a w ⊗ₜ[K]
        exteriorPower.ιMulti K b (fun j ↦ W.mkQ (v j))) =
      exteriorPower.ιMulti K (a + b) (Fin.append (fun i ↦ (w i : E)) v) := by
  apply (determinantCoordinateEquiv ((bW.sumQuot bQ).reindex finSumFinEquiv)).injective
  simp only [determinantSequenceEquivOfBases, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, TensorProduct.lid_tmul,
    LinearEquiv.apply_symm_apply, determinantCoordinateEquiv_ιMulti, smul_eq_mul]
  exact (sumQuot_fin_det W bW bQ w v).symm

include bW bQ in
/-- The wedge output is unchanged when any quotient lift is changed. -/
theorem ιMulti_append_eq_of_mkQ_eq (w : Fin a → W)
    (v v' : Fin b → E) (hv : ∀ j, W.mkQ (v j) = W.mkQ (v' j)) :
    exteriorPower.ιMulti K (a + b) (Fin.append (fun i ↦ (w i : E)) v) =
      exteriorPower.ιMulti K (a + b) (Fin.append (fun i ↦ (w i : E)) v') := by
  rw [← determinantSequenceEquivOfBases_ιMulti W bW bQ w v,
    ← determinantSequenceEquivOfBases_ιMulti W bW bQ w v']
  rw [funext hv]

/-- The actual determinant-line map is independent of both adapted bases. -/
theorem determinantSequenceEquivOfBases_eq
    (bW' : Module.Basis (Fin a) K W) (bQ' : Module.Basis (Fin b) K (E ⧸ W)) :
    determinantSequenceEquivOfBases W bW bQ =
      determinantSequenceEquivOfBases W bW' bQ' := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have hx : x = determinantCoordinateEquiv bW x • exteriorPower.ιMulti K a bW := by
    rw [← determinantCoordinateEquiv_symm,
      LinearEquiv.symm_apply_apply]
  have hy : y = determinantCoordinateEquiv bQ y • exteriorPower.ιMulti K b bQ := by
    rw [← determinantCoordinateEquiv_symm,
      LinearEquiv.symm_apply_apply]
  obtain ⟨v, hv⟩ : ∃ v : Fin b → E, ∀ j, W.mkQ (v j) = bQ j := by
    choose v hv using fun j ↦ W.mkQ_surjective (bQ j)
    exact ⟨v, hv⟩
  have he := determinantSequenceEquivOfBases_ιMulti W bW bQ bW v
  have he' := determinantSequenceEquivOfBases_ιMulti W bW' bQ' bW v
  rw [show (fun j ↦ W.mkQ (v j)) = bQ from funext hv] at he he'
  change determinantSequenceEquivOfBases W bW bQ (x ⊗ₜ[K] y) =
    determinantSequenceEquivOfBases W bW' bQ' (x ⊗ₜ[K] y)
  rw [hx, hy]
  simp only [TensorProduct.smul_tmul_smul, map_smul, he, he']

end Sequence

end ArakelovGeometry

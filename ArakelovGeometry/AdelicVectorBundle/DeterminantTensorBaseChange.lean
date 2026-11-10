/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.DeterminantTensorMap

/-!
# Completed scalar extension of the tensor determinant map

Canonical scalar extension, finite tensor-power transport and exterior
transport put the rational determinant tensor map on its actual completed
domain and codomain. No tensor norm comparison is part of this construction.
-/

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (E : Type*) [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (F : Type*) [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The canonical tensor determinant map on actual scalar-extended exterior
powers and their actual finite tensor powers. -/
def determinantTensorEquivCompleted :
    ((⨂[L] (_ : Fin (Module.finrank K F)),
      ⋀[L]^(Module.finrank K E) (L ⊗[K] E)) ⊗[L]
      (⨂[L] (_ : Fin (Module.finrank K E)),
        ⋀[L]^(Module.finrank K F) (L ⊗[K] F))) ≃ₗ[L]
      (⋀[L]^(Module.finrank K (E ⊗[K] F)) (L ⊗[K] (E ⊗[K] F))) :=
  ((TensorProduct.congr
    ((PiTensorProduct.congr (fun _ : Fin (Module.finrank K F) ↦
      (exteriorBaseChangeEquiv K L E (Module.finrank K E)).symm)).trans
        (tensorBaseChangeEquiv K L
          (fun _ : Fin (Module.finrank K F) ↦ ⋀[K]^(Module.finrank K E) E)).symm)
    ((PiTensorProduct.congr (fun _ : Fin (Module.finrank K E) ↦
      (exteriorBaseChangeEquiv K L F (Module.finrank K F)).symm)).trans
        (tensorBaseChangeEquiv K L
          (fun _ : Fin (Module.finrank K E) ↦ ⋀[K]^(Module.finrank K F) F)).symm)).trans
    (TensorProduct.AlgebraTensorModule.distribBaseChange K L _ _).symm).trans
      (((determinantTensorEquiv K E F).baseChange K L).trans
        (exteriorBaseChangeEquiv K L (E ⊗[K] F) (Module.finrank K (E ⊗[K] F))))

/-- Scalar extension preserves the determinant tensor wedge formula on all
original tuples, including empty and singular tuples. -/
theorem determinantTensorEquivCompleted_ιMulti_one_tmul
    (x : Fin (Module.finrank K E) → E) (y : Fin (Module.finrank K F) → F) :
    determinantTensorEquivCompleted K L E F
      ((⨂ₜ[L] (_ : Fin (Module.finrank K F)),
        exteriorPower.ιMulti L (Module.finrank K E) (fun i ↦ (1 : L) ⊗ₜ[K] x i)) ⊗ₜ[L]
        (⨂ₜ[L] (_ : Fin (Module.finrank K E)),
          exteriorPower.ιMulti L (Module.finrank K F) (fun j ↦ (1 : L) ⊗ₜ[K] y j))) =
      exteriorPower.ιMulti L (Module.finrank K (E ⊗[K] F))
        (fun i ↦ (1 : L) ⊗ₜ[K]
          (x (finProdFinEquiv.symm ((finCongr
            (finrank_mul_eq_tensor K E F)).symm i)).1 ⊗ₜ[K]
          y (finProdFinEquiv.symm ((finCongr
            (finrank_mul_eq_tensor K E F)).symm i)).2)) := by
  simp only [determinantTensorEquivCompleted, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, PiTensorProduct.congr_tprod,
    exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one,
    tensorBaseChangeEquiv_symm_tprod_tmul,
    TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    one_mul, LinearEquiv.baseChange_tmul, determinantTensorEquiv_ιMulti,
    exteriorBaseChangeEquiv_tmul_ιMulti, one_smul]

/-- In every scalar field the completed map is the intrinsic tensor-basis
construction, followed by the canonical binary tensor base-change map.
The comparison is proved on generators of the actual powered lines. -/
theorem determinantTensorEquivCompleted_eq_of_bases
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (c : Module.Basis (Fin (Module.finrank K F)) K F) :
    (determinantTensorEquivCompleted K L E F).toLinearMap =
      exteriorPower.map (Module.finrank K (E ⊗[K] F))
        (TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm.toLinearMap ∘ₗ
      (exteriorPowerDegreeEquiv L ((L ⊗[K] E) ⊗[L] (L ⊗[K] F))
        (finrank_mul_eq_tensor K E F)).toLinearMap ∘ₗ
      (determinantTensorEquivOfBases (b.baseChange L) (c.baseChange L)).toLinearMap := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro t
  have hz : z = determinantPowerCoordinateEquiv (b.baseChange L) (Module.finrank K F) z •
      (⨂ₜ[L] (_ : Fin (Module.finrank K F)),
        exteriorPower.ιMulti L (Module.finrank K E) (b.baseChange L)) := by
    rw [← determinantPowerCoordinateEquiv_symm, LinearEquiv.symm_apply_apply]
  have ht : t = determinantPowerCoordinateEquiv (c.baseChange L) (Module.finrank K E) t •
      (⨂ₜ[L] (_ : Fin (Module.finrank K E)),
        exteriorPower.ιMulti L (Module.finrank K F) (c.baseChange L)) := by
    rw [← determinantPowerCoordinateEquiv_symm, LinearEquiv.symm_apply_apply]
  have hb : ⇑(b.baseChange L) = fun i ↦ (1 : L) ⊗ₜ[K] b i :=
    funext (b.baseChange_apply L)
  have hc : ⇑(c.baseChange L) = fun i ↦ (1 : L) ⊗ₜ[K] c i :=
    funext (c.baseChange_apply L)
  change determinantTensorEquivCompleted K L E F (z ⊗ₜ[L] t) =
    (exteriorPower.map (Module.finrank K (E ⊗[K] F))
        (TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm.toLinearMap ∘ₗ
      (exteriorPowerDegreeEquiv L ((L ⊗[K] E) ⊗[L] (L ⊗[K] F))
        (finrank_mul_eq_tensor K E F)).toLinearMap ∘ₗ
      (determinantTensorEquivOfBases (b.baseChange L) (c.baseChange L)).toLinearMap)
        (z ⊗ₜ[L] t)
  rw [hz, ht]
  simp only [TensorProduct.smul_tmul_smul, map_smul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, determinantTensorEquivOfBases_ιMulti,
    exteriorPowerDegreeEquiv_ιMulti, exteriorPower.map_apply_ιMulti,
    hb, hc, determinantTensorEquivCompleted_ιMulti_one_tmul,
    Function.comp_def, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    one_mul]

/-- The completed tensor determinant map has the ordered wedge formula for
arbitrary completed tuples, rather than only original rational tuples. -/
theorem determinantTensorEquivCompleted_ιMulti
    (x : Fin (Module.finrank K E) → L ⊗[K] E)
    (y : Fin (Module.finrank K F) → L ⊗[K] F) :
    determinantTensorEquivCompleted K L E F
      ((⨂ₜ[L] (_ : Fin (Module.finrank K F)),
        exteriorPower.ιMulti L (Module.finrank K E) x) ⊗ₜ[L]
        (⨂ₜ[L] (_ : Fin (Module.finrank K E)),
          exteriorPower.ιMulti L (Module.finrank K F) y)) =
      exteriorPower.ιMulti L (Module.finrank K (E ⊗[K] F))
        (fun i ↦ (TensorProduct.AlgebraTensorModule.distribBaseChange K L E F).symm
          (x (finProdFinEquiv.symm ((finCongr
            (finrank_mul_eq_tensor K E F)).symm i)).1 ⊗ₜ[L]
          y (finProdFinEquiv.symm ((finCongr
            (finrank_mul_eq_tensor K E F)).symm i)).2)) := by
  have he := DFunLike.congr_fun (determinantTensorEquivCompleted_eq_of_bases K L E F
    (Module.finBasis K E) (Module.finBasis K F))
      ((⨂ₜ[L] (_ : Fin (Module.finrank K F)),
        exteriorPower.ιMulti L (Module.finrank K E) x) ⊗ₜ[L]
        (⨂ₜ[L] (_ : Fin (Module.finrank K E)),
          exteriorPower.ιMulti L (Module.finrank K F) y))
  simpa only [LinearEquiv.coe_coe, LinearMap.comp_apply,
    determinantTensorEquivOfBases_ιMulti, exteriorPowerDegreeEquiv_ιMulti,
    exteriorPower.map_apply_ιMulti, Function.comp_def] using he

end

end ArakelovGeometry
